-- Prove2me | solution 1 for OAI.edit_distance_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:19:48.762351+00:00
-- url     : https://prove2.me/submissions/dac2335a-9a6c-4d21-a27b-3f395f8f89cb

import Mathlib
import Definitions.Def_EditDistance
import Definitions.Def_OAIQ12Ed000

section
-- module Solutions.OAIQ12_ED.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem allow_substitution {x y : List Alpha} (h : Step false x y) : Step true x y := by
  cases h with
  | insert p q a => exact .insert p q a
  | delete p q a => exact .delete p q a
  | substitute hs => cases hs

end Step

namespace Script

theorem allow_substitution {n : ℕ} {x y : List Alpha} (h : Script false n x y) :
    Script true n x y := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact .cons e.allow_substitution ih

end Script



theorem cost_symm (x y : List Alpha) : cost s x y = cost s y x := by
  apply Nat.le_antisymm
  · exact cost_le (cost_spec y x).symm
  · exact cost_le (cost_spec x y).symm

theorem cost_triangle (x y z : List Alpha) : cost s x z ≤ cost s x y + cost s y z :=
  cost_le ((cost_spec x y).trans (cost_spec y z))

theorem edit_le_indel (x y : List Alpha) : edit x y ≤ indel x y :=
  cost_le ((cost_spec (s := false) x y).allow_substitution)

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem Step.indel_simulation {x y : List Alpha} (e : Step true x y) :
    ∃ n ≤ 2, Script false n x y := by
  cases e with
  | insert p q a => exact ⟨1, by omega, Script.single (.insert p q a)⟩
  | delete p q a => exact ⟨1, by omega, Script.single (.delete p q a)⟩
  | substitute _ p q a b =>
    exact ⟨2, le_rfl, (Script.single (.delete p q a)).trans
      (Script.single (.insert p q b))⟩

theorem Script.indel_simulation {m : ℕ} {x y : List Alpha} (h : Script true m x y) :
    ∃ n ≤ 2 * m, Script false n x y := by
  induction h with
  | nil x => exact ⟨0, le_rfl, .nil x⟩
  | cons e h ih =>
    obtain ⟨n, hn, sn⟩ := ih
    obtain ⟨k, hk, sk⟩ := e.indel_simulation
    exact ⟨k + n, by omega, sk.trans sn⟩

theorem indel_le_two_edit (x y : List Alpha) : indel x y ≤ 2 * edit x y := by
  obtain ⟨n, hn, hs⟩ := (cost_spec (s := true) x y).indel_simulation
  exact (cost_le hs).trans hn

theorem Script.max_length (x y : List Alpha) : Script true (max x.length y.length) x y := by
  induction x generalizing y with
  | nil => simpa using (Script.to_nil (s := true) y).symm
  | cons a x ih =>
    cases y with
    | nil => simpa using Script.to_nil (s := true) (a :: x)
    | cons b y =>
      have hs := (ih y).append_left [b]
      have he := Step.substitute rfl [] x a b
      simpa only [List.length_cons, max_add_add_right, List.singleton_append, List.nil_append] using
        Script.cons he hs

theorem edit_le_max_length (x y : List Alpha) : edit x y ≤ max x.length y.length :=
  cost_le (Script.max_length x y)

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Distance-ratio extrema and finite-dimensional embeddings
-/

namespace EditDistortion
universe u v

lemma ratios_finite {X : Type u} [Finite X] (ρ : X → X → ℝ) (f : X → L1) :
    {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}.Finite := by
  refine (Set.finite_range (fun p : X × X => ‖f p.1-f p.2‖/ρ p.1 p.2)).subset ?_
  rintro r ⟨x,y,_,rfl⟩
  exact Set.mem_range.mpr ⟨(x,y),rfl⟩

lemma reverse_ratios_finite {X : Type u} [Finite X] (ρ : X → X → ℝ) (f : X → L1) :
    {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}.Finite := by
  refine (Set.finite_range (fun p : X × X => ρ p.1 p.2/‖f p.1-f p.2‖)).subset ?_
  rintro r ⟨x,y,_,rfl⟩
  exact Set.mem_range.mpr ⟨(x,y),rfl⟩

lemma distortion_constants {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ distortion ρ f = U*V ∧
      (∀ x y, ‖f x-f y‖ ≤ U*ρ x y) ∧ (∀ x y, ρ x y ≤ V*‖f x-f y‖) := by
  let U := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}
  let V := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}
  have hu (x y : X) (hxy : x ≠ y) : ‖f x-f y‖/ρ x y ≤ U :=
    le_csSup (ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩
  have hv (x y : X) (hxy : x ≠ y) : ρ x y/‖f x-f y‖ ≤ V :=
    le_csSup (reverse_ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩
  have hn (x y : X) (hxy : x ≠ y) : 0 < ‖f x-f y‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (f.injective h)))
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  refine ⟨U,V,(div_pos (hn x y hxy) (hp x y hxy)).trans_le (hu x y hxy),
    (div_pos (hp x y hxy) (hn x y hxy)).trans_le (hv x y hxy),rfl,?_,?_⟩
  · intro x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self,norm_zero,hd,mul_zero,le_refl]
    · exact (div_le_iff₀ (hp x y hxy)).mp (hu x y hxy)
  · intro x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self,norm_zero,hd,mul_zero,le_refl]
    · exact (div_le_iff₀ (hn x y hxy)).mp (hv x y hxy)

lemma distortion_nonneg {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) : 0 ≤ distortion ρ f := by
  obtain ⟨U,V,hU,hV,he,_,_⟩ := distortion_constants ρ hd hp f
  rw [he]
  positivity

lemma leastDistortion_lower {X : Type u} [Fintype X] (ρ : X → X → ℝ) (B : ℝ)
    (h : ∀ f : X ↪ L1, B ≤ distortion ρ f) : B ≤ leastDistortion ρ := by
  let : Nonempty (X ↪ L1) := ⟨coordinateEmbedding X⟩
  apply le_csInf (Set.range_nonempty (f := distortion ρ))
  rintro r ⟨f,rfl⟩
  exact h f

lemma finite_words (Alpha : Type u) [Finite Alpha] (d : ℕ) : Finite (Words Alpha d) := by
  let domain := (n : Fin (d+1)) × (Fin n.val → Alpha)
  let F : domain → Words Alpha d := fun ⟨n,v⟩ => ⟨List.ofFn v,by simp only [List.length_ofFn]; omega⟩
  apply Finite.of_surjective F
  intro x
  refine ⟨⟨⟨x.val.length,by have := x.property; omega⟩,x.val.get⟩,?_⟩
  apply Subtype.ext
  exact List.ofFn_get x.val

lemma edit_real_diag {Alpha : Type u} (x : List Alpha) : (edit x x : ℝ) = 0 := by
  exact_mod_cast (cost_refl (s := true) x)

lemma edit_real_pos {Alpha : Type u} (x y : List Alpha) (hxy : x ≠ y) : 0 < (edit x y : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt (cost_eq_zero_iff (s := true)).mp hxy)

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DistortionMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restriction and monotonicity of least distortion
-/

namespace EditDistortion
universe u v

lemma leastDistortion_le {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) : leastDistortion ρ ≤ distortion ρ f := by
  apply csInf_le (s := Set.range (distortion ρ)) (a := distortion ρ f) ?_ ⟨f,rfl⟩
  refine ⟨0,?_⟩
  rintro r ⟨g,rfl⟩
  exact distortion_nonneg ρ hd hp g

lemma distortion_le_of_bounds {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hp : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X ↪ L1) {U V : ℝ} (hU : 0 ≤ U)
    (hu : ∀ x y, ‖f x-f y‖ ≤ U*ρ x y)
    (hv : ∀ x y, ρ x y ≤ V*‖f x-f y‖) : distortion ρ f ≤ U*V := by
  have hn (x y : X) (hxy : x ≠ y) : 0 < ‖f x-f y‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (f.injective h)))
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have hn1 : {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}.Nonempty :=
    ⟨_,⟨x,y,hxy,rfl⟩⟩
  have hn2 : {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}.Nonempty :=
    ⟨_,⟨x,y,hxy,rfl⟩⟩
  have h1 : sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y} ≤ U := by
    apply csSup_le hn1
    rintro r ⟨i,j,hij,rfl⟩
    exact (div_le_iff₀ (hp i j hij)).mpr (hu i j)
  have h2 : sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖} ≤ V := by
    apply csSup_le hn2
    rintro r ⟨i,j,hij,rfl⟩
    exact (div_le_iff₀ (hn i j hij)).mpr (hv i j)
  have hnon : 0 ≤ sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖} :=
    (div_nonneg (hp x y hxy).le (norm_nonneg _)).trans
      (le_csSup (reverse_ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩)
  unfold distortion
  exact mul_le_mul h1 h2 hnon hU

theorem leastDistortion_mono {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    [Nontrivial X] [Nontrivial Y] (ρX : X → X → ℝ) (ρY : Y → Y → ℝ)
    (hdX : ∀ x, ρX x x = 0) (hpX : ∀ x y, x ≠ y → 0 < ρX x y)
    (hdY : ∀ x, ρY x x = 0) (hpY : ∀ x y, x ≠ y → 0 < ρY x y)
    (e : X ↪ Y) (he : ∀ x y, ρY (e x) (e y) = ρX x y) :
    leastDistortion ρX ≤ leastDistortion ρY := by
  apply leastDistortion_lower
  intro f
  obtain ⟨U,V,hU,_,hD,hu,hv⟩ := distortion_constants ρY hdY hpY f
  let g : X ↪ L1 := e.trans f
  calc
    leastDistortion ρX ≤ distortion ρX g := leastDistortion_le ρX hdX hpX g
    _ ≤ U*V := distortion_le_of_bounds ρX hpX g hU.le
      (fun x y => by simpa only [g,Function.Embedding.trans_apply,he] using hu (e x) (e y))
      (fun x y => by simpa only [g,Function.Embedding.trans_apply,he] using hv (e x) (e y))
    _ = distortion ρY f := hD.symm

end EditDistortion

namespace EditDistortion
universe u

theorem binary_subset_lower (Alpha : Type u) [Fintype Alpha] (hAlpha : 2 ≤ Fintype.card Alpha)
    {d n : ℕ} (hn : n ≤ d) (S : Set (List Bool)) (hfin : S.Finite) (hnt : S.Nontrivial)
    (hlen : ∀ w ∈ S, w.length = n) :
    leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) ≤ E Alpha d := by
  classical
  let : Fintype S := hfin.fintype
  let : Nontrivial S := hnt.coe_sort
  let : Finite (Words Alpha d) := finite_words Alpha d
  let : Fintype (Words Alpha d) := Fintype.ofFinite _
  let a : Bool ↪ Alpha := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_bool] using hAlpha))
  let e : S ↪ Words Alpha d :=
    ⟨fun x => ⟨x.val.map a,by simpa only [List.length_map,hlen x.val x.property] using hn⟩,
      fun x y h => Subtype.ext ((List.map_inj_right a.injective).mp (congrArg Subtype.val h))⟩
  let : Nontrivial (Words Alpha d) := by
    obtain ⟨x,y,hxy⟩ := exists_pair_ne S
    exact ⟨⟨e x,e y,fun h => hxy (e.injective h)⟩⟩
  apply leastDistortion_mono _ _
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h)))
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) e
  intro x y
  exact_mod_cast cost_map_eq_of_leftInverse (s := true) a (Function.invFun a)
    (Function.leftInverse_invFun a.injective) x.val y.val

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FamilyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Length, alphabet, and distortion recurrences for word families
-/

namespace EditFamily
open scoped BigOperators

lemma familyAlphabet_pos {b P : ℕ} (hP : 0 < P) (s : ℕ) : 0 < familyAlphabet b P s := by
  cases s <;> simp only [familyAlphabet] <;> omega

lemma familyAlphabet_le {b P : ℕ} (hb : 0 < b) (hP : 0 < P) (s : ℕ) :
    familyAlphabet b P s ≤ (2 * P + 1) * (2 * b) ^ s := by
  induction s with
  | zero => simp [familyAlphabet]
  | succ s ih =>
      have hap := familyAlphabet_pos (b := b) hP s
      have hb' : 2 * b - 1 + 1 = 2 * b := by omega
      calc
        familyAlphabet b P (s+1) = 1 + (2 * b - 1) * familyAlphabet b P s := rfl
        _ ≤ 2 * b * familyAlphabet b P s := by
          nlinarith [Nat.mul_add (2 * b - 1) 1 (familyAlphabet b P s)]
        _ ≤ 2 * b * ((2 * P + 1) * (2 * b) ^ s) := Nat.mul_le_mul_left _ ih
        _ = (2 * P + 1) * (2 * b) ^ (s+1) := by rw [pow_succ]; ring

end EditFamily

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_PrimePool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite pools of distinct primes from central binomial estimates
-/

namespace EditPrimes
open scoped BigOperators
open Nat Finset

lemma centralBinom_le_with_primes (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^(Nat.sqrt (2*n)) * 4^(2*n/3) * (2*n)^(pool n).card := by
  have hpos : 0 < n := by omega
  have h2pos : 1 ≤ 2*n := by omega
  let f (p : ℕ) := p ^ n.centralBinom.factorization p
  let S := (Finset.range (2*n+1)).filter Nat.Prime
  let T := (Finset.range (2*n/3+1)).filter Nat.Prime
  have heq : n.centralBinom = ∏ p ∈ S, f p := by
    rw [← n.prod_pow_factorization_centralBinom]
    dsimp [S,f]
    symm
    apply Finset.prod_filter_of_ne
    intro p _ h
    contrapose h
    rw [Nat.factorization_eq_zero_of_not_prime _ h,pow_zero]
  have hlow : ∏ p ∈ S.filter (· ≤ n), f p = ∏ p ∈ T, f p := by
    symm
    apply Finset.prod_subset
    · intro p hp
      obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
      have hb := Finset.mem_range.mp hp
      have hm : 2*n/3 ≤ n := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩,by omega⟩
    · intro p hp hpT
      obtain ⟨hp,hpn⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,hprime⟩ := Finset.mem_filter.mp hp
      have hb : 2*n/3 < p := by
        by_contra h
        apply hpT
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩
      have hb' : 2*n < 3*p := by omega
      dsimp [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hb',pow_zero]
  have hhigh : S.filter (fun p => ¬p ≤ n) = pool n := by
    ext p
    simp only [S,pool,Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc,Nat.lt_succ_iff,not_le]
    tauto
  have hT : ∏ p ∈ T, f p ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) := by
    rw [←Finset.prod_filter_mul_prod_filter_not T (· ≤ Nat.sqrt (2*n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' (fun p _ => (show f p ≤ 2*n from
        Nat.pow_factorization_choose_le (by omega)))).trans ?_
      rw [Finset.prod_const]
      apply Nat.pow_le_pow_right h2pos
      have hc : (Finset.Icc 1 (Nat.sqrt (2*n))).card = Nat.sqrt (2*n) := by
        rw [Nat.card_Icc,Nat.add_sub_cancel]
      apply (Finset.card_le_card ?_).trans hc.le
      intro p hp
      obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_lt.le,hs⟩
    · refine le_trans ?_ (primorial_le_four_pow (2*n/3))
      refine (Finset.prod_le_prod' (fun p hp => (show f p ≤ p from ?_))).trans ?_
      · obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
        dsimp [f]
        refine (Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hs))
      · apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        intro p hp _
        exact (Finset.mem_filter.mp hp).2.one_lt.le
  rw [heq,←Finset.prod_filter_mul_prod_filter_not S (· ≤ n),hlow,hhigh]
  apply Nat.mul_le_mul hT
  calc
    ∏ p ∈ pool n, f p ≤ ∏ _p ∈ pool n, (2*n) :=
      Finset.prod_le_prod' (fun _ _ => Nat.pow_factorization_choose_le (by omega))
    _ = (2*n)^(pool n).card := Finset.prod_const _

end EditPrimes

namespace EditPrimes
open scoped BigOperators
open Nat Finset Filter

lemma binomial_log_bound {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 < Real.log (n : ℝ) +
      ((Nat.sqrt (2*n) : ℝ) + (pool n).card) * Real.log (2*(n : ℝ)) +
        (2*(n : ℝ)/3) * Real.log 4 := by
  have hb := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hu := centralBinom_le_with_primes n (by omega)
  have hr : (4 : ℝ)^n < (n : ℝ) *
      ((2*(n : ℝ))^(Nat.sqrt (2*n)) * 4^(2*n/3) * (2*(n : ℝ))^(pool n).card) := by
    exact_mod_cast hb.trans_le (Nat.mul_le_mul_left n hu)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have h2n : 0 < 2*(n : ℝ) := by positivity
  have hl := Real.log_lt_log (by positivity : 0 < (4 : ℝ)^n) hr
  rw [Real.log_mul hnR.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hl
  simp only [Real.log_pow] at hl
  have hf : ((2*n/3 : ℕ) : ℝ) ≤ 2*(n : ℝ)/3 := by
    have h := (Nat.cast_div_le (m := 2*n) (n := 3) : ((2*n/3 : ℕ) : ℝ) ≤ ((2*n : ℕ) : ℝ)/(3 : ℝ))
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hf hlog]

lemma pool_square_large {b : ℕ} (hb : 2 ≤ b)
    (hlog : Real.log (b : ℝ) ≤ (Real.log 4 / 60) * (b : ℝ)) : b ≤ (pool (b^2)).card := by
  by_contra hcard
  have hcard : (pool (b^2)).card ≤ b := by omega
  have h := binomial_log_bound (show 4 ≤ b^2 by nlinarith)
  have bpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : Nat.sqrt (2*(b^2)) ≤ 2*b := by
    have hsq := Nat.sqrt_le (2*b^2)
    nlinarith
  have hsR : (Nat.sqrt (2*b^2) : ℝ) ≤ 2*(b : ℝ) := by exact_mod_cast hs
  have hcR : ((pool (b^2)).card : ℝ) ≤ b := by exact_mod_cast hcard
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (b : ℝ) := Real.log_le_log (by norm_num) hbR
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : Real.log ((b^2 : ℕ) : ℝ) = 2 * Real.log (b : ℝ) := by
    simp only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
  have hlog2n : Real.log (2 * ((b^2 : ℕ) : ℝ)) ≤ 3 * Real.log (b : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity),hlogn]
    linarith
  have hlog2np : 0 ≤ Real.log (2*((b^2 : ℕ) : ℝ)) := Real.log_nonneg (by push_cast; nlinarith)
  have hterm : ((Nat.sqrt (2*b^2) : ℝ) + (pool (b^2)).card) * Real.log (2*((b^2 : ℕ) : ℝ)) ≤
      9 * (b : ℝ) * Real.log (b : ℝ) := by
    calc
      _ ≤ (3 * (b : ℝ)) * (3*Real.log (b : ℝ)) := by gcongr; linarith
      _ = _ := by ring
  rw [hlogn] at h
  push_cast at h hterm
  have hsmall : 2*Real.log (b : ℝ) + 9*(b : ℝ)*Real.log (b : ℝ) ≤ 10*(b : ℝ)*Real.log (b : ℝ) := by
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 10*(b : ℝ) by positivity)
  nlinarith [sq_pos_of_pos bpos]

theorem eventually_pool_square : ∀ᶠ b : ℕ in Filter.atTop, b ≤ (pool (b^2)).card := by
  have hε : 0 < Real.log (4 : ℝ) / 60 := by positivity
  have hh := Real.isLittleO_log_id_atTop.def hε
  have hn : Filter.Tendsto (fun b : ℕ => (b : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually hh,Filter.eventually_ge_atTop (2 : ℕ)] with b hlog hb
  apply pool_square_large hb
  have hbn : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbn
  simpa only [Function.id_def,Real.norm_eq_abs,abs_of_nonneg hlogb,
    abs_of_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b)] using hlog

theorem primes_of_pool {b : ℕ} (hb : b ≤ (pool (b^2)).card) :
    ∃ p : Fin b → ℕ, Function.Injective p ∧
      (∀ j, (p j).Prime) ∧ (∀ j, b^2 ≤ p j) ∧ (∀ j, p j ≤ 2*b^2) := by
  classical
  let e : Fin b ↪ (pool (b^2)) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin,Fintype.card_coe] using hb))
  refine ⟨fun j => (e j).val, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro j
    exact (Finset.mem_filter.mp (e j).property).2
  · intro j
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (e j).property).1).1.le
  · intro j
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (e j).property).1).2

end EditPrimes

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_LowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive parameter bounds and exponential lower scales
-/

namespace EditParameters
open EditFamily

lemma prime_parameter_pos {k : ℕ} (hk : 0 < k) : 0 < P k := by
  unfold P b
  positivity

lemma eta_numerator_bound {k : ℕ} (hk : 0 < k) :
    2 * (2 * P k) ^ (2 * h k) * (h k)^k ≤ (P k) ^ (b k / 2) := by
  have hp : 4 ≤ P k := by dsimp [P,b]; nlinarith
  have hh : h k ≤ P k := by dsimp [h,P,b]; nlinarith
  have hpow : (2 * P k)^2 ≤ (P k)^3 := by nlinarith
  have he1 : 2*h k = 2*(10*k) := by rfl
  have he2 : b k / 2 = 50*k := by dsimp [b]; omega
  have htwo : 2 ≤ (P k)^k := le_trans (by omega : 2 ≤ P k)
    (Nat.le_self_pow (by omega) _)
  calc
    2 * (2*P k)^(2*h k) * (h k)^k ≤
        (P k)^k * ((P k)^3)^(10*k) * (P k)^k := by
          rw [he1,pow_mul]
          gcongr
    _ = (P k)^(32*k) := by rw [←pow_mul,←pow_add,←pow_add]; congr 1; omega
    _ ≤ (P k)^(b k / 2) := Nat.pow_le_pow_right (by omega) (by rw [he2]; omega)

lemma eta_le {k : ℕ} (hk : 0 < k) : eta k ≤ 1 / (h k : ℝ)^k := by
  have hp : (0 : ℝ) < ((P k)^(b k/2) : ℕ) := by
    exact_mod_cast pow_pos (prime_parameter_pos hk) _
  have hh : (0 : ℝ) < (h k : ℝ)^k := by dsimp [h]; positivity
  apply (div_le_div_iff₀ hp hh).mpr
  simpa only [one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    (show (2 : ℝ) * (2*(P k : ℝ))^(2*h k) * (h k : ℝ)^k ≤ ((P k)^(b k/2) : ℕ) by
      exact_mod_cast eta_numerator_bound hk)

lemma budget_bound {k : ℕ} (hk : 0 < k) (s : ℕ) :
    familyBudget (b k) (P k) (h k) s ≤ 2/(h k : ℝ)^s + 2*eta k := by
  have hp : (0 : ℝ) < h k := by dsimp [h]; positivity
  have htwo : (2 : ℝ) ≤ h k := by exact_mod_cast (show 2 ≤ h k by dsimp [h]; omega)
  have he : 0 ≤ eta k := by dsimp [eta]; positivity
  induction s with
  | zero => simp only [familyBudget,pow_zero,div_one]; linarith
  | succ s ih =>
    change eta k + familyBudget (b k) (P k) (h k) s / h k ≤ _
    calc
      _ ≤ eta k + (2/(h k : ℝ)^s+2*eta k)/(h k) := by gcongr
      _ = 2/(h k : ℝ)^(s+1) + (eta k + 2*eta k/(h k)) := by
        rw [pow_succ]; field_simp; ring
      _ ≤ 2/(h k : ℝ)^(s+1) + 2*eta k := by
        have ht : 2*eta k/(h k) ≤ eta k := (div_le_iff₀ hp).mpr (by nlinarith)
        linarith

theorem budget_small {k : ℕ} (hk : 0 < k) :
    familyBudget (b k) (P k) (h k) k ≤ 4/(h k : ℝ)^k := by
  have h1 := budget_bound hk k
  have h2 := eta_le hk
  simp only [div_eq_mul_inv,one_mul] at *
  linarith

lemma alphabet_power_bound {k : ℕ} (hk : 0 < k) :
    familyAlphabet (b k) (P k) k ≤ 2^(30*k^2) := by
  have hb : 0 < b k := by dsimp [b]; omega
  have hp : 0 < P k := prime_parameter_pos hk
  have hkb : k ≤ 2^k := Nat.lt_two_pow_self.le
  have hbpow : 2*b k ≤ 2^(k+8) := by
    simp only [pow_add]
    norm_num only [show 2^8=256 by norm_num]
    dsimp [b]
    nlinarith
  have hppow : 2*P k+1 ≤ 2^(2*k+16) := by
    calc
      2*P k+1 ≤ (2*b k)^2 := by dsimp [P]; nlinarith
      _ ≤ (2^(k+8))^2 := Nat.pow_le_pow_left hbpow 2
      _ = _ := by rw [←pow_mul]; congr 1; ring
  calc
    familyAlphabet (b k) (P k) k ≤ (2*P k+1)*(2*b k)^k := familyAlphabet_le hb hp k
    _ ≤ 2^(2*k+16)*(2^(k+8))^k := Nat.mul_le_mul hppow (Nat.pow_le_pow_left hbpow k)
    _ = 2^(k^2+10*k+16) := by rw [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^(30*k^2) := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma bits_poly {k : ℕ} (hk : 0 < k) : codeBits k ≤ 30*k^2 :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (alphabet_power_bound hk)

lemma width_poly {k : ℕ} (hk : 0 < k) : codeWidth k ≤ 63*k^2 := by
  have ht := bits_poly hk
  dsimp [codeWidth]
  nlinarith

lemma width_pos (k : ℕ) : 0 < codeWidth k := by dsimp [codeWidth]; omega
lemma encodedLength_pos {k : ℕ} (hk : 0 < k) : 0 < encodedLength k :=
  Nat.mul_pos (width_pos k) (familyLength_pos (by dsimp [b]; omega) (prime_parameter_pos hk) k)

lemma length_power_bound (k : ℕ) : familyLength (b k) (P k) k ≤
    (4*(b k)^(100*k+1))^k := by
  have he : b k / 2 = 50*k := by dsimp [b]; omega
  unfold familyLength
  apply Nat.pow_le_pow_left
  calc
    2*(2*b k-1)*(P k)^(b k/2) ≤ 4*b k*(P k)^(b k/2) :=
      Nat.mul_le_mul_right _ (by have := Nat.sub_le (2*b k) 1; omega)
    _ = 4*(b k)^(100*k+1) := by
      dsimp [P]
      rw [he,←pow_mul,pow_succ]
      have he' : 2*(50*k)=100*k := by omega
      rw [he']
      ring

theorem log_length_bound {k : ℕ} (hk : 2 ≤ k) :
    Real.log (encodedLength k : ℝ) ≤ 1000*(k : ℝ)^2*Real.log (k : ℝ) := by
  have hkpos : 0 < k := by omega
  have kr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have kp : (0 : ℝ) < k := by positivity
  have bp : (0 : ℝ) < b k := by dsimp [b]; positivity
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have np : (0 : ℝ) < familyLength (b k) (P k) k := by
    exact_mod_cast familyLength_pos (by dsimp [b]; omega) (prime_parameter_pos hkpos) k
  have lk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have l2 : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) kr
  have l63 : Real.log (63 : ℝ) ≤ 6*Real.log (2 : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<63) (by norm_num : (63 : ℝ) ≤ 2^6)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have l100 : Real.log (100 : ℝ) ≤ 7*Real.log (2 : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<100) (by norm_num : (100 : ℝ) ≤ 2^7)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have l4 : Real.log (4 : ℝ) = 2*Real.log (2 : ℝ) := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have lb : Real.log (b k : ℝ) ≤ 8*Real.log (k : ℝ) := by
    simp only [b,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) kp.ne']
    linarith
  have lw : Real.log (codeWidth k : ℝ) ≤ 8*Real.log (k : ℝ) := by
    have hw : (codeWidth k : ℝ) ≤ 63*(k : ℝ)^2 := by exact_mod_cast width_poly hkpos
    have hl := Real.log_le_log wp hw
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have ln : Real.log (familyLength (b k) (P k) k : ℝ) ≤
      (k : ℝ)*(Real.log (4 : ℝ)+(100*(k : ℝ)+1)*Real.log (b k : ℝ)) := by
    have hn : (familyLength (b k) (P k) k : ℝ) ≤
        (4*(b k : ℝ)^(100*k+1))^k := by exact_mod_cast length_power_bound k
    have hl := Real.log_le_log np hn
    rw [Real.log_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
    push_cast at hl
    exact hl
  have he : Real.log (encodedLength k : ℝ) =
      Real.log (codeWidth k : ℝ)+Real.log (familyLength (b k) (P k) k : ℝ) := by
    simp only [encodedLength,Nat.cast_mul,Real.log_mul wp.ne' np.ne']
  rw [he]
  calc
    _ ≤ 8*Real.log (k : ℝ)+(k : ℝ)*(2*Real.log (k : ℝ)+
        (100*(k : ℝ)+1)*(8*Real.log (k : ℝ))) := by
      apply add_le_add lw
      apply ln.trans
      gcongr
      linarith
    _ = (800*(k : ℝ)^2+10*(k : ℝ)+8)*Real.log (k : ℝ) := by ring
    _ ≤ 1000*(k : ℝ)^2*Real.log (k : ℝ) := by
      gcongr
      nlinarith

lemma log_width_le {k : ℕ} (hk : 0 < k) :
    Real.log (codeWidth k : ℝ) ≤ Real.log (63 : ℝ)+2*Real.log (k : ℝ) := by
  have hw : (codeWidth k : ℝ) ≤ 63*(k : ℝ)^2 := by exact_mod_cast width_poly hk
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.log_le_log wp hw
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

theorem ratio_exponential {k : ℕ} (hk : 24^4 ≤ k) :
    Real.exp ((1/2 : ℝ)*(k : ℝ)*Real.log (k : ℝ)) ≤ lowerRatio k := by
  have hk0 : 0 < k := by norm_num at hk; omega
  have kp : (0 : ℝ) < k := by exact_mod_cast hk0
  have k12 : (12 : ℝ) ≤ k := by exact_mod_cast (show 12 ≤ k by norm_num at hk; omega)
  have k1008 : (1008 : ℝ) ≤ k := by exact_mod_cast (show 1008 ≤ k by norm_num at hk; omega)
  have hn : (0 : ℝ) < h k := by dsimp [h]; positivity
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have rp : 0 < lowerRatio k := by dsimp [lowerRatio]; positivity
  apply (Real.le_log_iff_exp_le rp).mp
  have lkp : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have l24 : 4*Real.log (24 : ℝ) ≤ Real.log (k : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<24^4)
      (show (24 : ℝ)^4 ≤ k by exact_mod_cast hk)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have lh : Real.log (k : ℝ) ≤ Real.log (h k : ℝ) := by
    apply Real.log_le_log kp
    dsimp [h]; push_cast; nlinarith
  have lw := log_width_le hk0
  have lconst : Real.log (16 : ℝ)+Real.log (63 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]
    norm_num only [show (16 : ℝ)*63=1008 by norm_num]
    exact Real.log_le_log (by norm_num) k1008
  have logeq : Real.log (lowerRatio k) =
      (k : ℝ)*(Real.log (h k : ℝ)-Real.log (24 : ℝ))-
        (Real.log (16 : ℝ)+Real.log (codeWidth k : ℝ)) := by
    dsimp [lowerRatio]
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,
      Real.log_div hn.ne' (by norm_num),Real.log_mul (by norm_num) wp.ne']
  rw [logeq]
  have h1 := mul_le_mul_of_nonneg_left lh kp.le
  have h2 := mul_le_mul_of_nonneg_left l24 kp.le
  have h3 : 12*Real.log (k : ℝ) ≤ (k : ℝ)*Real.log (k : ℝ) :=
    mul_le_mul_of_nonneg_right k12 lkp
  nlinarith

end EditParameters

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DepthInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverting recursive depth for all sufficiently large lengths
-/

namespace EditDepth
open Filter

lemma radius_nonneg (t : ℝ) : 0 ≤ radius t := Real.sqrt_nonneg _

lemma eventually_radius_large (K : ℕ) :
    ∀ᶠ t : ℝ in atTop, (100 : ℝ)*(K+2) ≤ radius t := by
  let R : ℝ := 100*((K : ℝ)+2)
  have hR : 0 < R := by dsimp [R]; positivity
  have he : 0 < 1/R^2 := by positivity
  have hlog := Real.isLittleO_log_id_atTop.def he
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog,hl,eventually_ge_atTop (1 : ℝ)] with t ht hlt htp
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have ht' : Real.log t ≤ t/R^2 := by
    simpa only [Function.id_def,Real.norm_eq_abs,abs_of_pos tp,abs_of_pos lp,div_eq_mul_inv,one_mul,mul_comm] using ht
  have hs : R^2 ≤ t/Real.log t := by
    apply (le_div_iff₀ lp).mpr
    have hb := (le_div_iff₀ (sq_pos_of_pos hR)).mp ht'
    nlinarith
  exact Real.le_sqrt_of_sq_le hs

lemma depth_lower {t : ℝ} (ht : 200 ≤ radius t) : radius t/200 ≤ (depth t : ℝ) := by
  have hf := Nat.lt_floor_add_one (radius t/100)
  change radius t/100 < (depth t : ℝ)+1 at hf
  linarith

lemma depth_upper (t : ℝ) : (depth t : ℝ) ≤ radius t/100 :=
  Nat.floor_le (div_nonneg (radius_nonneg t) (by norm_num))

lemma depth_bounds {t : ℝ} (ht : 1 ≤ t) (hlt : 1 ≤ Real.log t)
    (hr : 200 ≤ radius t) (hll : Real.log (Real.log t) ≤ Real.log t/6)
    (hlarge : 12*Real.log (200 : ℝ) ≤ Real.log t) :
    1000*(depth t : ℝ)^2*Real.log (depth t : ℝ) ≤ t ∧
      Real.sqrt (t*Real.log t)/1200 ≤ (1/2 : ℝ)*(depth t : ℝ)*Real.log (depth t : ℝ) := by
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have rp : 0 < radius t := by linarith
  have kp : 0 < (depth t : ℝ) := lt_of_lt_of_le (by positivity) (depth_lower hr)
  have hr2 : radius t^2 = t/Real.log t := Real.sq_sqrt (div_nonneg tp.le lp.le)
  have hr2' : radius t^2*Real.log t = t := (eq_div_iff lp.ne').mp hr2
  have hrle : radius t ≤ t := by
    have hdiv : t/Real.log t ≤ t := (div_le_iff₀ lp).mpr (by nlinarith)
    nlinarith [radius_nonneg t]
  have hkle : (depth t : ℝ) ≤ t := by
    have hh := depth_upper t
    nlinarith [radius_nonneg t]
  have logupper : Real.log (depth t : ℝ) ≤ Real.log t := Real.log_le_log kp hkle
  have loglower : Real.log t/3 ≤ Real.log (depth t : ℝ) := by
    have hlog := Real.log_le_log (by positivity : 0 < radius t/200) (depth_lower hr)
    have logR : Real.log (radius t) = (Real.log t - Real.log (Real.log t))/2 := by
      dsimp [radius]
      rw [Real.log_sqrt (div_nonneg tp.le lp.le),Real.log_div tp.ne' lp.ne']
    rw [Real.log_div rp.ne' (by norm_num),logR] at hlog
    linarith
  have hsq : (depth t : ℝ)^2 ≤ radius t^2/10000 := by
    have hh := depth_upper t
    nlinarith [sq_nonneg (radius t/100-(depth t : ℝ))]
  have hsqrt : Real.sqrt (t*Real.log t) = radius t*Real.log t := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log t) hr2']
  constructor
  · calc
      _ ≤ 1000*(depth t : ℝ)^2*Real.log t := mul_le_mul_of_nonneg_left logupper (by positivity)
      _ ≤ t := by
        have hh := mul_le_mul_of_nonneg_right hsq lp.le
        nlinarith
  · rw [hsqrt]
    have hh : radius t/200*(Real.log t/3) ≤ (depth t : ℝ)*Real.log (depth t : ℝ) := by
      gcongr
      · exact depth_lower hr
    linarith

theorem eventually_choose_depth (K : ℕ) : ∀ᶠ t : ℝ in atTop,
    K ≤ depth t ∧ 1000*(depth t : ℝ)^2*Real.log (depth t : ℝ) ≤ t ∧
      Real.sqrt (t*Real.log t)/1200 ≤ (1/2 : ℝ)*(depth t : ℝ)*Real.log (depth t : ℝ) := by
  have hsmall := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ)<1/6)
  have hsmall' := Real.tendsto_log_atTop.eventually hsmall
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hh := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (12*Real.log (200 : ℝ)))
  filter_upwards [eventually_radius_large K,hsmall',hl,hh,eventually_ge_atTop (1 : ℝ)] with t hr hs hl hh ht
  have hK : (K : ℝ) ≤ radius t/100 := by nlinarith
  have hr' : 200 ≤ radius t := by have := Nat.cast_nonneg (α := ℝ) K; nlinarith
  have hll : Real.log (Real.log t) ≤ Real.log t/6 := by
    have hlog := Real.log_nonneg hl
    have hpos : 0 ≤ Real.log t := by linarith
    simpa only [Function.id_def,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg hpos,
      div_eq_mul_inv,one_mul,mul_comm] using hs
  exact ⟨Nat.le_floor hK,depth_bounds ht hl hr' hll hh⟩

end EditDepth

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DelimiterAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Increasing matchings through binary delimiter blocks
-/

namespace EditCode
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Matching
variable {k w n U V : ℕ} {f g : Fin k → ℕ}

lemma span_of_no_defect (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (hm : ¬ Missing f w i) (hgap : ¬ Gap f g w i) : BlockSpan f g w i := by
  have hfull : ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w * i + r := by
    intro r hr
    by_contra h
    exact hm ⟨r,hr,by simpa only [not_exists] using h⟩
  obtain ⟨a₀, ha₀⟩ := hfull 0 hw
  refine ⟨g a₀, ?_⟩
  intro r hr
  induction r with
  | zero => exact ⟨a₀,ha₀,by omega⟩
  | succ r ih =>
      obtain ⟨a, ha, hga⟩ := ih (by omega)
      obtain ⟨b, hb⟩ := hfull (r+1) hr
      have hab : a < b := hf.lt_iff_lt.mp (by omega)
      have hgab := hg hab
      have hn : ¬g a + 1 < g b := fun h => hgap ⟨r,a,b,hr,ha,hb,h⟩
      exact ⟨b,hb,by omega⟩

lemma defect_of_not_span (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (h : ¬BlockSpan f g w i) : Missing f w i ∨ Gap f g w i := by
  by_contra h'
  push Not at h'
  exact h (span_of_no_defect hf hg hw i h'.1 h'.2)

lemma exists_charge (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w) (i : ℕ)
    (h : ¬BlockSpan f g w i) : ∃ x, Charge f g w i x := by
  rcases defect_of_not_span hf hg hw i h with hm | hgap
  · obtain ⟨r,hr,hm⟩ := hm
    exact ⟨Sum.inl (w*i+r), by exact ⟨by omega,by omega,hm⟩⟩
  · obtain ⟨r,a,b,hr,ha,hb,hgap⟩ := hgap
    refine ⟨Sum.inr (g a+1), ?_⟩
    constructor
    · intro c hc
      have hac : a < c := hg.lt_iff_lt.mp (by omega)
      have hcb : c < b := hg.lt_iff_lt.mp (by omega)
      have hfa := hf hac
      have hfb := hf hcb
      omega
    · exact ⟨a,b,by omega,by omega,by omega,by omega,by omega,hgap⟩

lemma charge_distinct (hf : StrictMono f) (hg : StrictMono g)
    {i j : ℕ} (hij : i ≠ j) {x : ℕ ⊕ ℕ}
    (hi : Charge f g w i x) (hj : Charge f g w j x) : False := by
  wlog h : i < j generalizing i j
  · exact this hij.symm hj hi (lt_of_le_of_ne (Nat.le_of_not_gt h) hij.symm)
  have hwi : w * i + w ≤ w * j := by
    have := Nat.mul_le_mul_left w h
    nlinarith
  cases x with
  | inl x => dsimp [Charge] at hi hj; omega
  | inr x =>
      obtain ⟨_,a,b,ha₁,ha₂,hb₁,hb₂,hax,hxb⟩ := hi
      obtain ⟨_,c,d,hc₁,hc₂,hd₁,hd₂,hcx,hxd⟩ := hj
      have hbc : b < c := hf.lt_iff_lt.mp (by omega)
      have := hg hbc
      omega

lemma missing_card {N : ℕ} (hf : Function.Injective f) (hN : ∀ a, f a < N) :
    (Finset.range N \ Finset.univ.image f).card = N - k := by
  have hs : Finset.univ.image f ⊆ Finset.range N := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hN a)
  rw [Finset.card_sdiff_of_subset hs, Finset.card_range,
    Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem bad_blocks_le_loss
    (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w)
    (hU : ∀ a, f a < U) (hV : ∀ a, g a < V) (hn : w * n ≤ U) :
    (Finset.univ.filter (fun i : Fin n => ¬BlockSpan f g w i.val)).card ≤ (U-k) + (V-k) := by
  classical
  let B := {i : Fin n // ¬BlockSpan f g w i.val}
  let X := Finset.range U \ Finset.univ.image f
  let Y := Finset.range V \ Finset.univ.image g
  have hx (i : B) : ∃ x, Charge f g w i.val.val x := exists_charge hf hg hw i.val i.property
  let c (i : B) : ℕ ⊕ ℕ := (hx i).choose
  have hc (i : B) : Charge f g w i.val.val (c i) := (hx i).choose_spec
  have hcX (i : B) (x : ℕ) (he : c i = Sum.inl x) : x ∈ X := by
    have h := hc i
    rw [he] at h
    rcases h with ⟨h₁,h₂,h₃⟩
    have hwi : w * (i.val.val+1) ≤ w * n := Nat.mul_le_mul_left _ i.val.isLt
    simp only [X, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists]
    exact ⟨by nlinarith,fun a => (h₃ a)⟩
  have hcY (i : B) (x : ℕ) (he : c i = Sum.inr x) : x ∈ Y := by
    have h := hc i
    rw [he] at h
    obtain ⟨hx,a,b,_,_,_,_,_,hxb⟩ := h
    simp only [Y, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists]
    exact ⟨lt_trans hxb (hV b),hx⟩
  let c' (i : B) : X ⊕ Y := match he : c i with
    | Sum.inl x => Sum.inl ⟨x,hcX i x he⟩
    | Sum.inr x => Sum.inr ⟨x,hcY i x he⟩
  have hval (i : B) : Sum.map Subtype.val Subtype.val (c' i) = c i := by
    dsimp [c']
    split <;> rename_i x he <;> exact he.symm
  have hinj : Function.Injective c' := by
    intro i j he
    have he' : c i = c j := by rw [←hval i,←hval j,he]
    by_contra hij
    have hvalne : i.val.val ≠ j.val.val := by
      intro h
      apply hij
      exact Subtype.ext (Fin.ext h)
    exact charge_distinct hf hg hvalne (hc i) (by rw [he']; exact hc j)
  have hcard := Fintype.card_le_of_injective c' hinj
  simpa only [B, Fintype.card_subtype, Fintype.card_sum, Fintype.card_coe, X, Y,
    missing_card hf.injective hU, missing_card hg.injective hV] using hcard

end Matching
end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BinaryCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binary delimiter codes and padding
-/

namespace EditCode
open EditDistortion
variable {A : Type*} {t : ℕ}

lemma bit_label (label : A → Fin t → Bool) (a : A) (i : Fin t) :
    bit label a (2 * i.val + 3) = label a i := by
  have hm : (2 * i.val + 3) % 2 = 1 := by omega
  have hd : (2 * i.val + 3) / 2 - 1 = i.val := by omega
  simp [bit, show ¬2*i.val+3<2 by omega, hm, hd]

lemma bit_even (label : A → Fin t → Bool) (a : A) {r : ℕ}
    (hr : 2 ≤ r) (he : r % 2 = 0) : bit label a r = false := by
  simp [bit,show ¬r<2 by omega,he]

lemma bit_last (label : A → Fin t → Bool) (a : A) :
    bit label a (width t - 1) = false := by
  apply bit_even
  · unfold width; omega
  · unfold width; omega

lemma bit_consecutive (label : A → Fin t → Bool) {a : A} {r : ℕ}
    (h₁ : bit label a r = true) (h₂ : bit label a (r+1) = true) : r = 0 := by
  by_contra h
  by_cases he : r % 2 = 0
  · have hr : 2 ≤ r := by omega
    rw [bit_even label a hr he] at h₁
    cases h₁
  · have he : (r+1)%2=0 := by omega
    rw [bit_even label a (by omega) he] at h₂
    cases h₂

lemma encode_get_block (label : A → Fin t → Bool) (x : List A)
    (i : Fin x.length) (r : Fin (width t)) :
    (encode label x)[width t * i.val + r.val]'(by
      rw [encode_length]
      have hm := Nat.mul_le_mul_left (width t) i.isLt
      simp only [Nat.mul_succ] at hm
      have := r.isLt
      omega) = bit label (x.get i) r := by
  induction x with
  | nil => exact Fin.elim0 i
  | cons a x ih =>
    by_cases hi : i.val = 0
    · simp only [encode, List.flatMap_cons]
      rw [List.getElem_append_left (by simp [hi])]
      simp [block,hi,List.get_eq_getElem]
    · let j : Fin x.length := ⟨i.val-1,by simpa only [List.length_cons] using (show i.val-1<x.length by
        have := i.isLt; simp only [List.length_cons] at this; omega)⟩
      have hij : i.val = j.val+1 := by dsimp [j]; omega
      simp only [encode, List.flatMap_cons]
      rw [List.getElem_append_right (by rw [block_length]; rw [hij]; nlinarith)]
      simp only [block_length]
      have he : width t * i.val + r.val - width t = width t * j.val + r.val := by rw [hij,Nat.mul_add,Nat.mul_one]; omega
      simp only [he]
      have hget : (a :: x).get i = x.get j := by
        simp only [List.get_eq_getElem,hij,List.getElem_cons_succ]
      rw [hget]
      exact ih j

lemma padded_get_block (label : A → Fin t → Bool) (x : List A) (pad : ℕ)
    (i : Fin x.length) (r : Fin (width t)) :
    (padded label x pad)[width t * i.val + r.val]'(by
      rw [padded_length]
      have hm := Nat.mul_le_mul_left (width t) i.isLt
      simp only [Nat.mul_succ] at hm
      have := r.isLt
      omega) = bit label (x.get i) r := by
  unfold padded
  rw [List.getElem_append_left (by
    rw [encode_length]
    have hm := Nat.mul_le_mul_left (width t) i.isLt
    simp only [Nat.mul_succ] at hm
    have := r.isLt
    omega),encode_get_block]

lemma padded_get_padding (label : A → Fin t → Bool) (x : List A) (pad n : ℕ)
    (hn : n < (padded label x pad).length) (hp : width t * x.length ≤ n) :
    (padded label x pad)[n] = false := by
  unfold padded at hn ⊢
  rw [List.getElem_append_right (by simpa using hp)]
  simp

lemma padded_delimiter (label : A → Fin t → Bool) (x : List A) (pad n : ℕ)
    (hn : n+1 < (padded label x pad).length)
    (h₁ : (padded label x pad)[n]'(by omega) = true)
    (h₂ : (padded label x pad)[n+1] = true) :
    ∃ i : Fin x.length, n = width t * i.val := by
  have hnp : n < width t * x.length := by
    by_contra h
    rw [padded_get_padding label x pad n (by omega) (by omega)] at h₁
    cases h₁
  let i : Fin x.length := ⟨n / width t, (Nat.div_lt_iff_lt_mul width_pos).mpr (by nlinarith)⟩
  let r : Fin (width t) := ⟨n % width t, Nat.mod_lt _ width_pos⟩
  have hnE : n = width t * i.val + r.val := by
    dsimp [i,r]
    have := Nat.mod_add_div n (width t)
    omega
  have hrLast : r.val ≠ width t - 1 := by
    intro he
    have h := padded_get_block label x pad i r
    simp only [←hnE] at h
    have hb := bit_last label (x.get i)
    simp only [show (r : ℕ) = width t-1 from he,hb] at h
    rw [h] at h₁
    cases h₁
  let r' : Fin (width t) := ⟨r.val+1,by have := r.isLt; omega⟩
  have hb₁ : bit label (x.get i) r = true := by
    have hv := padded_get_block label x pad i r
    simp only [←hnE] at hv
    exact hv.symm.trans h₁
  have hb₂ : bit label (x.get i) (r.val+1) = true := by
    rw [← padded_get_block label x pad i r']
    have he : width t*i.val+r'.val=n+1 := by dsimp [r']; omega
    simpa only [he] using h₂
  have hr0 := bit_consecutive label hb₁ hb₂
  exact ⟨i,by omega⟩

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BlockAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contraction of arbitrary bit alignments to letter blocks
-/

namespace EditCode
open EditDistortion
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} {t k : ℕ}

lemma BlockPair.symm {f g : Fin k → ℕ} {w i j : ℕ} (h : BlockPair f g w i j) :
    BlockPair g f w j i := by
  intro r hr
  obtain ⟨a,ha,hb⟩ := h r hr
  exact ⟨a,hb,ha⟩

lemma BlockPair.span {f g : Fin k → ℕ} {w i j : ℕ} (h : BlockPair f g w i j) :
    BlockSpan f g w i := ⟨w*j,h⟩

lemma pair_strict {f g : Fin k → ℕ} {w i j i' j' : ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w)
    (h : BlockPair f g w i j) (h' : BlockPair f g w i' j') (hi : i < i') : j < j' := by
  obtain ⟨a,ha,hga⟩ := h 0 hw
  obtain ⟨b,hb,hgb⟩ := h' 0 hw
  have hab : a < b := hf.lt_iff_lt.mp (by simpa only [ha,hb,Nat.add_zero] using Nat.mul_lt_mul_of_pos_left hi hw)
  have := hg hab
  nlinarith

lemma pair_unique {f g : Fin k → ℕ} {w i j j' : ℕ}
    (hf : Function.Injective f) (hw : 0 < w)
    (h : BlockPair f g w i j) (h' : BlockPair f g w i j') : j = j' := by
  obtain ⟨a,ha,hga⟩ := h 0 hw
  obtain ⟨b,hb,hgb⟩ := h' 0 hw
  have hab : a = b := hf (ha.trans hb.symm)
  rw [hab] at hga
  nlinarith

lemma span_pair (label : A → Fin t → Bool) (x y : List A) (r s : ℕ)
    {f g : Fin k → ℕ}
    (hf : ∀ a, f a < (padded label x r).length)
    (hg : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hf a) = (padded label y s)[g a]'(hg a))
    (i : Fin x.length) (hi : BlockSpan f g (width t) i.val) :
    ∃ j : Fin y.length, BlockPair f g (width t) i.val j.val := by
  obtain ⟨q,hq⟩ := hi
  obtain ⟨a,ha,hga⟩ := hq 0 width_pos
  obtain ⟨b,hb,hgb⟩ := hq 1 (by unfold width; omega)
  have hqLen : q+1 < (padded label y s).length := by rw [←hgb]; exact hg b
  have hq₀ : (padded label y s)[q]'(by omega) = true := by
    have he := heq a
    have hv := padded_get_block label x r i ⟨0,width_pos⟩
    simp only [bit_zero,Nat.add_zero] at hv
    simpa only [ha,hga,Nat.add_zero,hv] using he.symm
  have hq₁ : (padded label y s)[q+1] = true := by
    have he := heq b
    have hv := padded_get_block label x r i ⟨1,by unfold width; omega⟩
    simp only [bit_one] at hv
    simpa only [hb,hgb,hv] using he.symm
  obtain ⟨j,hj⟩ := padded_delimiter label y s q hqLen hq₀ hq₁
  refine ⟨j,?_⟩
  intro a ha
  simpa only [hj] using hq a ha

lemma pair_letters (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) {f g : Fin k → ℕ}
    (hf : ∀ a, f a < (padded label x r).length)
    (hg : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hf a) = (padded label y s)[g a]'(hg a))
    (i : Fin x.length) (j : Fin y.length) (h : BlockPair f g (width t) i.val j.val) :
    x.get i = y.get j := by
  apply hinj
  funext v
  have hv : 2*v.val+3<width t := by unfold width; omega
  obtain ⟨a,ha,hb⟩ := h (2*v.val+3) hv
  have he := heq a
  have hx := padded_get_block label x r i ⟨2*v.val+3,hv⟩
  have hy := padded_get_block label y s j ⟨2*v.val+3,hv⟩
  simp only [ha,hb,hx,hy] at he
  simpa only [bit_label] using he

end EditCode

namespace EditCode
open EditDistortion
attribute [local instance] Classical.propDecidable
variable {A : Type*} {t k : ℕ}

theorem letter_loss_le (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g)
    (hfB : ∀ a, f a < (padded label x r).length)
    (hgB : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hfB a) = (padded label y s)[g a]'(hgB a)) :
    indel x y ≤ 2 * (((padded label x r).length-k) + ((padded label y s).length-k)) := by
  classical
  let K := Finset.univ.filter (fun i : Fin x.length => BlockSpan f g (width t) i.val)
  let B := {i : Fin x.length // BlockSpan f g (width t) i.val}
  let C := {j : Fin y.length // BlockSpan g f (width t) j.val}
  have hpair (i : B) : ∃ j : Fin y.length, BlockPair f g (width t) i.val j.val :=
    span_pair label x y r s hfB hgB heq i.val i.property
  let next (i : B) : Fin y.length := (hpair i).choose
  have next_pair (i : B) : BlockPair f g (width t) i.val (next i).val := (hpair i).choose_spec
  let e : Fin K.card ↪o Fin x.length := K.orderEmbOfFin rfl
  have he (i : Fin K.card) : BlockSpan f g (width t) (e i).val :=
    (Finset.mem_filter.mp (K.orderEmbOfFin_mem rfl i)).2
  let q (i : Fin K.card) : Fin y.length := next ⟨e i,he i⟩
  have hq : StrictMono q := by
    intro i j hij
    exact pair_strict hf hg width_pos (next_pair ⟨e i,he i⟩) (next_pair ⟨e j,he j⟩)
      (e.strictMono hij)
  have hletter : ∀ i, x.get (e i) = y.get (q i) := by
    intro i
    exact pair_letters label hinj x y r s hfB hgB heq _ _ (next_pair ⟨e i,he i⟩)
  have hcost := indel_le_of_matching x.get y.get e (OrderEmbedding.ofStrictMono q hq) hletter
  simp only [List.ofFn_get] at hcost
  have hback (j : C) : ∃ i : Fin x.length, BlockPair g f (width t) j.val i.val :=
    span_pair label y x s r hgB hfB (fun a => (heq a).symm) j.val j.property
  let back (j : C) : B := ⟨(hback j).choose,(hback j).choose_spec.symm.span⟩
  have hbackinj : Function.Injective back := by
    intro j j' he
    have hh : (hback j).choose.val = (hback j').choose.val :=
      congrArg (fun i : B => i.val.val) he
    apply Subtype.ext
    apply Fin.ext
    apply pair_unique hf.injective width_pos (hback j).choose_spec.symm
    rw [hh]
    exact (hback j').choose_spec.symm
  have hcard := Fintype.card_le_of_injective back hbackinj
  have hcard' : (Finset.univ.filter (fun j : Fin y.length => BlockSpan g f (width t) j.val)).card ≤ K.card := by
    simpa only [B,C,Fintype.card_subtype,K] using hcard
  have hbadX := bad_blocks_le_loss hf hg width_pos hfB hgB
    (show width t * x.length ≤ (padded label x r).length by simp)
  have hbadY := bad_blocks_le_loss hg hf width_pos hgB hfB
    (show width t * y.length ≤ (padded label y s).length by simp)
  have hsplitX := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin x.length => BlockSpan f g (width t) i.val)
  have hsplitY := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun j : Fin y.length => BlockSpan g f (width t) j.val)
  simp only [Finset.card_univ,Fintype.card_fin] at hsplitX hsplitY
  change K.card + _ = _ at hsplitX
  omega

theorem indel_code_lower (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) :
    indel x y ≤ 2 * indel (padded label x r) (padded label y s) := by
  obtain ⟨z,hx,hy,hcost⟩ := indel_matching (padded label x r) (padded label y s)
  obtain ⟨f,hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g,hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  have h := letter_loss_le label hinj x y r s
    (f := fun a => (f a).val) (g := fun a => (g a).val)
    (fun _ _ h => f.strictMono h) (fun _ _ h => g.strictMono h)
    (fun a => (f a).isLt) (fun a => (g a).isLt)
    (fun a => (hf a).symm.trans (hg a))
  have hzX := hx.length_le
  have hzY := hy.length_le
  have he : (padded label x r).length-z.length + ((padded label y s).length-z.length) =
      (padded label x r).length+(padded label y s).length-2*z.length := by omega
  rwa [he,←hcost] at h

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_BinaryEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-length binary embeddings with unrestricted edit distance
-/

namespace EditDistortion
variable {A B : Type*}

lemma Script.flatMap {n w : ℕ} {x y : List A} (h : Script false n x y)
    (c : A → List B) (hc : ∀ a, (c a).length = w) :
    Script false (w*n) (x.flatMap c) (y.flatMap c) := by
  induction h with
  | nil x => simpa using Script.nil (substitutions := false) (x.flatMap c)
  | @cons n x y z first rest ih =>
    have he : Script false w (x.flatMap c) (y.flatMap c) := by
      cases first with
      | insert p q a =>
        have h := ((Script.to_nil (s := false) (c a)).symm.append_left (p.flatMap c)).append_right (q.flatMap c)
        simpa only [hc,List.append_nil,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h
      | delete p q a =>
        have h := ((Script.to_nil (s := false) (c a)).append_left (p.flatMap c)).append_right (q.flatMap c)
        simpa only [hc,List.append_nil,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h
      | substitute hf => cases hf
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using he.trans ih

lemma indel_flatMap_le (c : A → List B) (w : ℕ) (hc : ∀ a, (c a).length = w) (x y : List A) :
    indel (x.flatMap c) (y.flatMap c) ≤ w * indel x y :=
  cost_le ((cost_spec (s := false) x y).flatMap c hc)

end EditDistortion

namespace EditCode
open EditDistortion
variable {A : Type*} {t : ℕ}

theorem indel_code_upper (label : A → Fin t → Bool) (x y : List A) :
    indel (encode label x) (encode label y) ≤ width t * indel x y :=
  indel_flatMap_le (block label) (width t) (block_length label) x y

end EditCode

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_LowerDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Distortion lower bounds from separated finite word families
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditAverage EditFourier

variable {p n A t : ℕ} {α Q : ℝ} (F : Family p n A α Q)
  (label : Fin A ↪ (Fin t → Bool))

lemma codeSet_finite : (codeSet F label).Finite := Set.finite_range _
lemma codeSet_nonempty : (codeSet F label).Nonempty := ⟨_,⟨0,rfl⟩⟩
lemma codeSet_length (x : List Bool) (hx : x ∈ codeSet F label) : x.length = width t*n := by
  obtain ⟨z,rfl⟩ := hx
  simp only [codeWord,encode_length,List.length_ofFn]

lemma far_after_code (hp : 1 < p) (z : F.State) :
    (n : ℝ)*α ≤ 4*(edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by
  have hf := F.far z 1 (by omega) hp
  simp only [one_nsmul] at hf
  have hc := indel_code_lower label label.injective (List.ofFn (F.word z))
    (List.ofFn (F.word (z+F.v))) 0 0
  simp only [padded,List.replicate_zero,List.append_nil] at hc
  have he := indel_le_two_edit (codeWord F label z) (codeWord F label (z+F.v))
  have hcR : (indel (List.ofFn (F.word z)) (List.ofFn (F.word (z+F.v))) : ℝ) ≤
      2*(indel (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by exact_mod_cast hc
  have heR : (indel (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) ≤
      2*(edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by exact_mod_cast he
  linarith

lemma codeSet_nontrivial (hp : 1 < p) (hn : 0 < n) (ha : 0 < α) : Nontrivial (codeSet F label) := by
  have h := far_after_code F label hp 0
  refine ⟨⟨codePoint F label 0,codePoint F label (0+F.v),?_⟩⟩
  intro he
  have he' : codeWord F label 0 = codeWord F label (0+F.v) := congrArg Subtype.val he
  rw [←he',edit_real_diag] at h
  have : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

theorem family_distortion (hp : 1 < p) (hn : 0 < n) (ha : 0 < α)
    (f : codeSet F label ↪ L1) :
    α ≤ 4*(width t : ℝ)*Q*distortion (fun x y : codeSet F label => (edit x.val y.val : ℝ)) f := by
  classical
  let : Fintype (codeSet F label) := (codeSet_finite F label).fintype
  let : Nontrivial (codeSet F label) := codeSet_nontrivial F label hp hn ha
  let ρ : codeSet F label → codeSet F label → ℝ := fun x y => (edit x.val y.val : ℝ)
  obtain ⟨U,V,hU,hV,hD,hu,hv⟩ := distortion_constants ρ
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) f
  let C : ℝ := U*(width t : ℝ)*n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hwR : (0 : ℝ) < width t := by exact_mod_cast EditCode.width_pos (t := t)
  have hC : 0 < C := by dsimp [C]; positivity
  let H : F.State → L1 := fun z => C⁻¹ • f (codePoint F label z)
  have hnorm (z e : F.State) : ‖H (z+e)-H z‖ =
      ‖f (codePoint F label (z+e))-f (codePoint F label z)‖/C := by
    simp only [H,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC),div_eq_mul_inv,mul_comm]
  have hnorm' (z e : F.State) : ‖f (codePoint F label (z+e))-f (codePoint F label z)‖ =
      C*‖H (z+e)-H z‖ := by rw [hnorm]; field_simp
  have hcheap (e : F.State) (r : ℝ) (hr : (e,r) ∈ F.steps) : variation H e ≤ r := by
    unfold variation
    rw [←avg_const (X := F.State) r]
    apply avg_mono
    intro z
    rw [hnorm,div_le_iff₀ hC,norm_sub_rev]
    have h1 := hu (codePoint F label z) (codePoint F label (z+e))
    have h2 := edit_le_indel (codeWord F label z) (codeWord F label (z+e))
    have h3 := indel_code_upper label (List.ofFn (F.word z)) (List.ofFn (F.word (z+e)))
    have h23 : (edit (codeWord F label z) (codeWord F label (z+e)) : ℝ) ≤
        (width t : ℝ)*(indel (List.ofFn (F.word z)) (List.ofFn (F.word (z+e))) : ℝ) := by
      exact_mod_cast h2.trans h3
    have h4 := F.cheap e r hr z
    change ‖f (codePoint F label z)-f (codePoint F label (z+e))‖ ≤
      U*(edit (codeWord F label z) (codeWord F label (z+e)) : ℝ) at h1
    calc
      _ ≤ U*((width t : ℝ)*((n : ℝ)*r)) := h1.trans (mul_le_mul_of_nonneg_left
        (h23.trans (mul_le_mul_of_nonneg_left h4 hwR.le)) hU.le)
      _ = r*C := by dsimp [C]; ring
  have hbound := F.control H hcheap 1 (by omega) hp
  simp only [one_nsmul] at hbound
  have hfar (z : F.State) : (n : ℝ)*α ≤ 4*V*C*‖H (z+F.v)-H z‖ := by
    have h1 := far_after_code F label hp z
    have h2 := hv (codePoint F label z) (codePoint F label (z+F.v))
    change (edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) ≤
      V*‖f (codePoint F label z)-f (codePoint F label (z+F.v))‖ at h2
    rw [norm_sub_rev,hnorm'] at h2
    nlinarith
  have havg : (n : ℝ)*α ≤ 4*V*C*variation H F.v := by
    change (n : ℝ)*α ≤ 4*V*C*avg (fun z => ‖H (z+F.v)-H z‖)
    rw [←avg_mul,←avg_const (X := F.State) ((n : ℝ)*α)]
    exact avg_mono hfar
  have hfinal : (n : ℝ)*α ≤ (n : ℝ)*(4*(width t : ℝ)*Q*(U*V)) := by
    calc
      _ ≤ 4*V*C*Q := havg.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
      _ = _ := by dsimp [C]; ring
  have hcancel := (mul_le_mul_iff_right₀ hnR).mp hfinal
  change α ≤ 4*(width t : ℝ)*Q*distortion ρ f
  rw [hD]
  exact hcancel

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_FiniteLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite nonempty binary witnesses of a common length
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditParameters

theorem family_ratio {k p : ℕ} (hk : 0 < k) (hp : 1 < p)
    (F : Family p (familyLength (b k) (P k) k) (familyAlphabet (b k) (P k) k)
      (familyAlpha k) (familyBudget (b k) (P k) (h k) k))
    (f : codeSet F (binaryLabels k) ↪ L1) :
    lowerRatio k ≤ distortion (fun x y : codeSet F (binaryLabels k) => (edit x.val y.val : ℝ)) f := by
  classical
  let label := binaryLabels k
  let : Fintype (codeSet F label) := (codeSet_finite F label).fintype
  have hn := familyLength_pos (by dsimp [b]; omega : 0 < b k) (prime_parameter_pos hk) k
  let : Nontrivial (codeSet F label) := codeSet_nontrivial F label hp hn (familyAlpha_pos k)
  let D := distortion (fun x y : codeSet F label => (edit x.val y.val : ℝ)) f
  have hD : 0 ≤ D := distortion_nonneg _ (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) f
  have hl := family_distortion F label hp hn (familyAlpha_pos k) f
  change familyAlpha k ≤ 4*(codeWidth k : ℝ)*familyBudget (b k) (P k) (h k) k*D at hl
  have hw : (0 : ℝ) < codeWidth k := by exact_mod_cast EditParameters.width_pos k
  have hh : (0 : ℝ) < (h k : ℝ)^k := by dsimp [h]; positivity
  have hb : familyAlpha k ≤ (16*(codeWidth k : ℝ)*D)/(h k : ℝ)^k := by
    calc
      _ ≤ 4*(codeWidth k : ℝ)*(4/(h k : ℝ)^k)*D := by
        apply hl.trans
        gcongr
        exact budget_small hk
      _ = _ := by ring
  have hmul := (le_div_iff₀ hh).mp hb
  have hpow : familyAlpha k*(h k : ℝ)^k = ((h k : ℝ)/24)^k := by
    unfold familyAlpha
    rw [←mul_pow]
    congr 1
    ring
  change ((h k : ℝ)/24)^k/(16*(codeWidth k : ℝ)) ≤ D
  apply (div_le_iff₀ (by positivity : 0 < 16*(codeWidth k : ℝ))).mpr
  rw [hpow] at hmul
  nlinarith

theorem eventually_depth_witness : ∀ᶠ k : ℕ in Filter.atTop,
    ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧ S.Nontrivial ∧
      (∀ w ∈ S, w.length = encodedLength k) ∧
      lowerRatio k ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) := by
  classical
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp EditPrimes.eventually_pool_square
  filter_upwards [Filter.eventually_ge_atTop (max 1 B)] with k hk
  have hk0 : 0 < k := by omega
  have hb0 : 0 < b k := by dsimp [b]; omega
  have hpool := hB (b k) (by dsimp [b]; omega)
  obtain ⟨p,hinj,hprime,hlow,hhigh⟩ := EditPrimes.primes_of_pool hpool
  have hP : 1 ≤ P k := Nat.one_le_iff_ne_zero.mpr (prime_parameter_pos hk0).ne'
  let j : Fin (b k) := ⟨0,hb0⟩
  let F : Family (p j) (familyLength (b k) (P k) k) (familyAlphabet (b k) (P k) k)
      (familyAlpha k) (familyBudget (b k) (P k) (h k) k) := by
    simpa only [Fintype.card_fin] using recursive p hprime hinj (P k) hP hlow hhigh
      (h k) (by dsimp [h]; omega) k j
  let S := codeSet F (binaryLabels k)
  let : Fintype S := (codeSet_finite F (binaryLabels k)).fintype
  refine ⟨S,codeSet_finite F (binaryLabels k),codeSet_nonempty F (binaryLabels k),?_,?_,?_⟩
  · exact Set.nontrivial_coe_sort.mp (codeSet_nontrivial F (binaryLabels k) (hprime j).one_lt
      (familyLength_pos hb0 (prime_parameter_pos hk0) k) (familyAlpha_pos k))
  · intro w hw
    exact codeSet_length F (binaryLabels k) w hw
  · apply leastDistortion_lower
    intro f
    exact family_ratio hk0 (hprime j).one_lt F f

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binary witnesses for every sufficiently large length bound
-/

namespace EditLower

universe u

open EditDistortion EditParameters Filter

theorem eventually_length_witness : ∀ᶠ d : ℕ in atTop,
    ∃ n : ℕ, n ≤ d ∧ ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧ S.Nontrivial ∧
      (∀ w ∈ S, w.length = n) ∧
      exponentScale (1/1200) d ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventually_depth_witness
  let J := max (max K (24^4)) 2
  have hlim : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hchoose := hlim.eventually (EditDepth.eventually_choose_depth J)
  filter_upwards [hchoose,eventually_ge_atTop 1] with d hd hd1
  let k := EditDepth.depth (Real.log (d : ℝ))
  have hk : J ≤ k := hd.1
  have hkK : K ≤ k := (le_max_left K (24^4)).trans ((le_max_left _ _).trans hk)
  have hk24 : 24^4 ≤ k := (le_max_right K (24^4)).trans ((le_max_left _ _).trans hk)
  have hk2 : 2 ≤ k := (le_max_right _ _).trans hk
  have hk0 : 0 < k := by omega
  obtain ⟨S,hfin,hne,hnt,hlen,hD⟩ := hK k hkK
  have hn : encodedLength k ≤ d := by
    have hlog : Real.log (encodedLength k : ℝ) ≤ Real.log (d : ℝ) :=
      (log_length_bound hk2).trans hd.2.1
    have hnp : (0 : ℝ) < encodedLength k := by exact_mod_cast encodedLength_pos hk0
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd1
    exact_mod_cast (Real.log_le_log_iff hnp hdp).mp hlog
  refine ⟨encodedLength k,hn,S,hfin,hne,hnt,hlen,?_⟩
  apply le_trans ?_ ((ratio_exponential hk24).trans hD)
  apply Real.exp_le_exp.mpr
  simpa only [div_eq_mul_inv,mul_comm,one_mul,k] using hd.2.2

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_AlphabetLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform lower bounds under binary alphabet embeddings
-/

namespace EditDistortion
universe u

lemma coordinate_norm {X : Type u} [Fintype X] (x : X) : ‖coordinateEmbedding X x‖ = 1 := by
  classical
  change ‖lp.single (E := fun _ : ℕ => ℝ) 1 ((Fintype.equivFin X x).val) (1 : ℝ)‖ = 1
  rw [lp.norm_single (by norm_num)]
  norm_num

lemma coordinate_separation {X : Type u} [Fintype X] (x y : X) (hxy : x ≠ y) :
    1 ≤ ‖coordinateEmbedding X x-coordinateEmbedding X y‖ := by
  classical
  let e : X ↪ ℕ := (Fintype.equivFin X).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  have hne : e x ≠ e y := fun h => hxy (e.injective h)
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (coordinateEmbedding X x - coordinateEmbedding X y) (e x)
  have he : (coordinateEmbedding X x-coordinateEmbedding X y) (e x) = 1 := by
    change lp.single (E := fun _ : ℕ => ℝ) 1 (e x) (1 : ℝ) (e x) -
      lp.single (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) (e x) = 1
    rw [lp.single_apply_self,lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) hne]
    norm_num
  simpa only [he,norm_one] using h

theorem alphabet_coarse_upper (Alpha : Type u) [Fintype Alpha] [Nonempty Alpha]
    {d : ℕ} (hd : 1 ≤ d) : E Alpha d ≤ 2*(d : ℝ) := by
  classical
  let : Finite (Words Alpha d) := finite_words Alpha d
  let : Fintype (Words Alpha d) := Fintype.ofFinite _
  let x : Words Alpha d := ⟨[],by simp⟩
  let y : Words Alpha d := ⟨[Classical.arbitrary Alpha],by simpa using hd⟩
  let : Nontrivial (Words Alpha d) := ⟨⟨x,y,by simp [x,y]⟩⟩
  let f := coordinateEmbedding (Words Alpha d)
  apply (leastDistortion_le _ (fun v => edit_real_diag v.val)
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f).trans
  apply distortion_le_of_bounds _
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f (by norm_num)
  · intro v w
    by_cases h : v = w
    · subst w
      simp [edit_real_diag]
    · have hp : (1 : ℝ) ≤ edit v.val w.val := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (mt (cost_eq_zero_iff (s := true)).mp (fun hh => h (Subtype.ext hh)))
      have hh := norm_sub_le (f v) (f w)
      have hv : ‖f v‖ = 1 := coordinate_norm v
      have hw : ‖f w‖ = 1 := coordinate_norm w
      nlinarith
  · intro v w
    by_cases h : v = w
    · subst w
      simp [edit_real_diag]
    · have hs : (1 : ℝ) ≤ ‖f v-f w‖ := coordinate_separation v w h
      have he : (edit v.val w.val : ℝ) ≤ d := by
        exact_mod_cast (edit_le_max_length v.val w.val).trans
          (max_le v.property w.property)
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

lemma alphabet_values_bddAbove {d : ℕ} (hd : 1 ≤ d) :
    BddAbove {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d} := by
  refine ⟨2*(d : ℝ),?_⟩
  rintro r ⟨n,hn,rfl⟩
  let : NeZero n := ⟨by omega⟩
  exact alphabet_coarse_upper (Fin n) hd

lemma alphabet_le_sup {d n : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n) : E (Fin n) d ≤ alphabetSup d :=
  le_csSup (alphabet_values_bddAbove hd) ⟨n,hn,rfl⟩

end EditDistortion

namespace EditLower

universe u

open EditDistortion

theorem all_lower_clauses : ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d) ∧ BinaryWitness c d ∧
      exponentScale c d ≤ alphabetSup d := by
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp eventually_length_witness
  refine ⟨1/1200,by norm_num,max D 1,?_⟩
  intro d hd
  obtain ⟨n,hn,S,hfin,hne,hnt,hlen,hs⟩ := hD d ((le_max_left _ _).trans hd)
  refine ⟨?_,⟨n,hn,S,hfin,hne,hlen,hs⟩,?_⟩
  · intro Alpha inst hAlpha
    exact hs.trans (binary_subset_lower Alpha hAlpha hn S hfin hnt hlen)
  · exact (hs.trans (binary_subset_lower (Fin 2) (by simp) hn S hfin hnt hlen)).trans
      (alphabet_le_sup ((le_max_right _ _).trans hd) (by omega))

end EditLower

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_HashCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cut hashes and averaged separation
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

lemma sep_le_one {X : Type*} (x y : X) : sep x y ≤ 1 := by unfold sep; split <;> norm_num
lemma sep_eq_one {X : Type*} {x y : X} (h : x ≠ y) : sep x y = 1 := by simp [sep,h]

section Hash
variable {I X : Type*} [Fintype I]

omit [Fintype I] in
lemma coin_sum (w : I → ℝ) (a : ℝ) (i : I) : ∑ b : Bool, coin w a i b = 1 := by
  simp [coin]

lemma probability_sum (w : I → ℝ) (a : ℝ) : ∑ h : I → Bool, probability w a h = 1 := by
  classical
  unfold probability
  rw [←Fintype.prod_sum]
  simp only [coin_sum,prod_const_one]

lemma collision_indicator (c : I → X → Bool) (h : I → Bool) (x y : X) :
    (if key c h x = key c h y then (1 : ℝ) else 0) =
      ∏ i, if (h i && c i x) = (h i && c i y) then (1 : ℝ) else 0 := by
  classical
  by_cases he : key c h x = key c h y
  · rw [ite_eq_left he]
    have hh (i : I) : (h i && c i x) = (h i && c i y) := congrFun he i
    simp only [hh,ite_true,prod_const_one]
  · rw [ite_eq_right he]
    have hex : ∃ i, (h i && c i x) ≠ (h i && c i y) := by
      by_contra hn
      push Not at hn
      exact he (funext hn)
    obtain ⟨i,hi⟩ := hex
    symm
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

theorem collision_probability (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h *
      if key c h x = key c h y then (1 : ℝ) else 0) = Real.exp (-a*distance w c x y) := by
  classical
  simp_rw [collision_indicator,probability,←prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i : I) (b : Bool) => coin w a i b *
    (if (b && c i x) = (b && c i y) then (1 : ℝ) else 0))]
  have hf (i : I) : (∑ b : Bool, coin w a i b *
      if (b && c i x) = (b && c i y) then (1 : ℝ) else 0) =
      Real.exp (-a*(w i*sep (c i x) (c i y))) := by
    cases hx : c i x <;> cases hy : c i y <;> simp [coin,sep]
  simp_rw [hf]
  rw [←Real.exp_sum]
  congr 1
  simp only [distance,mul_sum]

lemma separation_probability (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h * sep (key c h x) (key c h y)) =
      1-Real.exp (-a*distance w c x y) := by
  classical
  have hs (h : I → Bool) : sep (key c h x) (key c h y) =
      1-(if key c h x = key c h y then (1 : ℝ) else 0) := by
    unfold sep
    split <;> norm_num
  simp_rw [hs,mul_sub,mul_one]
  rw [sum_sub_distrib,probability_sum,collision_probability]

lemma separation_bound (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (x y : X) :
    (∑ h : I → Bool, probability w a h * sep (key c h x) (key c h y)) ≤
      a*distance w c x y := by
  rw [separation_probability]
  have hh := Real.add_one_le_exp (-a*distance w c x y)
  linarith

end Hash
end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Histograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hash separation and finite histogram inequalities
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section Histogram
variable {J K : Type*} [Fintype J] [Fintype K]

omit [Fintype K] in
lemma hit_nonneg (a b : K) : 0 ≤ hit a b := by unfold hit; split <;> norm_num

omit [Fintype K] in
lemma count_nonneg (f : J → K) (z : K) : 0 ≤ count f z := sum_nonneg (fun _ _ => hit_nonneg _ _)
lemma histogramDistance_nonneg (f g : J → K) : 0 ≤ histogramDistance f g :=
  sum_nonneg (fun _ _ => abs_nonneg _)

lemma hit_sum (a : K) : ∑ z, hit a z = 1 := by
  classical
  simp [hit]

lemma count_sum (f : J → K) : ∑ z, count f z = Fintype.card J := by
  unfold count
  rw [sum_comm]
  simp only [hit_sum,sum_const,card_univ,nsmul_eq_mul,mul_one]

lemma hit_distance (a b : K) : ∑ z, |hit a z-hit b z| = 2*sep a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [sep]
  · have he (z : K) : |hit a z-hit b z| = hit a z+hit b z := by
      by_cases haz : a = z
      · subst z
        simp [hit,Ne.symm hab]
      · by_cases hbz : b = z
        · subst z
          simp [hit,hab]
        · simp [hit,haz,hbz]
    simp_rw [he]
    rw [sum_add_distrib,hit_sum,hit_sum,sep_eq_one hab]
    norm_num

lemma histogramDistance_le (f g : J → K) : histogramDistance f g ≤ 2*∑ j, sep (f j) (g j) := by
  unfold histogramDistance count
  simp_rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ z : K, ∑ j : J, |hit (f j) z-hit (g j) z| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _ = 2*∑ j, sep (f j) (g j) := by
      rw [sum_comm]
      simp_rw [hit_distance]
      rw [mul_sum]

lemma histogramDistance_disjoint (f g : J → K) (h : ∀ i j, f i ≠ g j) :
    histogramDistance f g = 2*(Fintype.card J : ℝ) := by
  have hzero (z : K) : count f z = 0 ∨ count g z = 0 := by
    by_cases hf : ∃ i, f i = z
    · obtain ⟨i,rfl⟩ := hf
      right
      unfold count
      apply sum_eq_zero
      intro j _
      exact ite_eq_right (Ne.symm (h i j))
    · left
      unfold count
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (fun he => hf ⟨i,he⟩)
  have he (z : K) : |count f z-count g z| = count f z+count g z := by
    rcases hzero z with hz|hz
    · rw [hz,zero_sub,abs_neg,abs_of_nonneg (count_nonneg g z),zero_add]
    · rw [hz,sub_zero,abs_of_nonneg (count_nonneg f z),add_zero]
  unfold histogramDistance
  simp_rw [he]
  rw [sum_add_distrib,count_sum,count_sum]
  ring

lemma histogramDistance_lower (f g : J → K) :
    2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (f i) (g j)) ≤
      histogramDistance f g := by
  classical
  by_cases h : ∀ i j, f i ≠ g j
  · rw [histogramDistance_disjoint f g h]
    have hz : (∑ i : J, ∑ j : J, hit (f i) (g j)) = 0 := by
      apply sum_eq_zero
      intro i _
      apply sum_eq_zero
      intro j _
      exact ite_eq_right (h i j)
    rw [hz]
    ring_nf
    rfl
  · push Not at h
    obtain ⟨i,j,hij⟩ := h
    have h1 : 1 ≤ ∑ k : J, hit (f i) (g k) := by
      have hh := single_le_sum (fun k _ => hit_nonneg (f i) (g k)) (mem_univ j)
      simpa only [hij,hit_self] using hh
    have h2 : (∑ k : J, hit (f i) (g k)) ≤ ∑ l : J, ∑ k : J, hit (f l) (g k) :=
      single_le_sum (fun l _ => sum_nonneg (fun k _ => hit_nonneg (f l) (g k))) (mem_univ i)
    have hh : 1-∑ l : J, ∑ k : J, hit (f l) (g k) ≤ 0 := by linarith
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hh).trans
      (histogramDistance_nonneg f g)

end Histogram
end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_MeanHistograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean histograms as finite cut distances
-/

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

section MeanHistogram
variable {I J X : Type*} [Fintype I] [Fintype J]

lemma meanHistogram_nonneg {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) : 0 ≤ meanHistogram w a c f g :=
  sum_nonneg (fun h _ => mul_nonneg (probability_nonneg hw ha h) (histogramDistance_nonneg _ _))

lemma meanHistogram_upper {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) :
    meanHistogram w a c f g ≤ 2*a*∑ j, distance w c (f j) (g j) := by
  calc
    _ ≤ ∑ h : I → Bool, probability w a h * (2*∑ j, sep (key c h (f j)) (key c h (g j))) :=
      sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (histogramDistance_le _ _) (probability_nonneg hw ha h))
    _ = 2*∑ j : J, ∑ h : I → Bool, probability w a h * sep (key c h (f j)) (key c h (g j)) := by
      simp_rw [mul_left_comm (probability w a _ : ℝ) 2,mul_sum]
      rw [sum_comm]
    _ ≤ 2*∑ j : J, a*distance w c (f j) (g j) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact sum_le_sum (fun j _ => separation_bound w a c (f j) (g j))
    _ = _ := by rw [←mul_sum]; ring

lemma mean_cross_collisions (w : I → ℝ) (a : ℝ) (c : I → X → Bool) (f g : J → X) :
    (∑ h : I → Bool, probability w a h *
      (∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j)))) =
      ∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j)) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply Eq.trans ?_ (collision_probability w a c (f i) (g j))
  apply sum_congr rfl
  intro h _
  congr 1
  by_cases he : key c h (f i) = key c h (g j) <;> simp [hit,he]

theorem meanHistogram_lower {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : J → X) {R : ℝ} (hR : ∀ i j, R ≤ distance w c (f i) (g j)) :
    2*(Fintype.card J : ℝ)*(1-(Fintype.card J : ℝ)^2*Real.exp (-a*R)) ≤
      meanHistogram w a c f g := by
  have hc : (∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j))) ≤
      (Fintype.card J : ℝ)^2*Real.exp (-a*R) := by
    calc
      _ ≤ ∑ _i : J, ∑ _j : J, Real.exp (-a*R) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left (hR i j) ha]
      _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring
  have hp : (∑ h : I → Bool, probability w a h *
      (2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j))))) ≤
      meanHistogram w a c f g :=
    sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (histogramDistance_lower _ _) (probability_nonneg hw ha h))
  have he : (∑ h : I → Bool, probability w a h *
      (2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, hit (key c h (f i)) (key c h (g j))))) =
      2*(Fintype.card J : ℝ)*(1-∑ i : J, ∑ j : J, Real.exp (-a*distance w c (f i) (g j))) := by
    simp_rw [mul_left_comm (probability w a _) (2*(Fintype.card J : ℝ))]
    rw [←mul_sum]
    congr 1
    simp_rw [mul_sub,mul_one]
    rw [sum_sub_distrib,probability_sum,mean_cross_collisions]
  rw [he] at hp
  apply le_trans ?_ hp
  gcongr

lemma rate_exp {s : ℕ} (hs : 0 < s) : Real.exp (-rate s*(s : ℝ)) = 1/(2*(s : ℝ)^2) := by
  have sp : (0 : ℝ) < s := by exact_mod_cast hs
  rw [rate,neg_mul,div_mul_cancel₀ _ sp.ne',Real.exp_neg,Real.exp_log (by positivity)]
  simp only [one_div]

lemma meanHistogram_separated {s : ℕ} (hs : 0 < s) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (c : I → X → Bool) (f g : Fin s → X)
    (hR : ∀ i j, (s : ℝ) ≤ distance w c (f i) (g j)) :
    (s : ℝ) ≤ meanHistogram w (rate s) c f g := by
  have hh := meanHistogram_lower hw (rate_nonneg hs) c f g hR
  rw [Fintype.card_fin,rate_exp hs] at hh
  have sp : (0 : ℝ) < s := by exact_mod_cast hs
  have he : 2*(s : ℝ)*(1-(s : ℝ)^2*(1/(2*(s : ℝ)^2))) = (s : ℝ) := by
    field_simp
    ring
  simpa only [he] using hh

end MeanHistogram
end EditCutHash

namespace EditCutHash
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

lemma histogramDistance_shift {K : Type*} [Fintype K] {s : ℕ}
    (f g : Fin (s+1) → K) (h : ∀ i : Fin s, f i.castSucc = g i.succ) :
    histogramDistance f g ≤ 2 := by
  have hc (z : K) : count f z-count g z = hit (f (Fin.last s)) z-hit (g 0) z := by
    unfold count
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
    simp_rw [h]
    ring
  unfold histogramDistance
  simp_rw [hc]
  rw [hit_distance]
  have hh := sep_le_one (f (Fin.last s)) (g 0)
  linarith

lemma meanHistogram_shift {I X : Type*} [Fintype I] {s : ℕ} (hs : 0 < s)
    {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) {a : ℝ} (ha : 0 ≤ a)
    (c : I → X → Bool) (f g : Fin s → X)
    (h : ∀ i : Fin (s-1), f ⟨i.val,by omega⟩ = g ⟨i.val+1,by omega⟩) :
    meanHistogram w a c f g ≤ 2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hd (r : I → Bool) : histogramDistance (fun i => key c r (f i)) (fun i => key c r (g i)) ≤ 2 := by
    apply histogramDistance_shift
    intro i
    congr 1
    exact h ⟨i.val,by omega⟩
  calc
    _ ≤ ∑ r : I → Bool, probability w a r * 2 :=
      sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hd r) (probability_nonneg hw ha r))
    _ = 2 := by rw [←sum_mul,probability_sum,one_mul]

end EditCutHash

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_CutModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted cuts and histogram lifts
-/

namespace EditCutModel

universe u v

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

attribute [instance] Model.finiteIndex

lemma Model.dist_symm {X : Type u} (M : Model X) (x y : X) : M.dist x y = M.dist y x := by
  unfold Model.dist
  apply sum_congr rfl
  intro i _
  simp [sep,eq_comm]

lemma Model.dist_triangle {X : Type u} (M : Model X) (x y z : X) :
    M.dist x z ≤ M.dist x y+M.dist y z := by
  unfold Model.dist
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left ?_ (M.nonneg i)
  cases M.cut i x <;> cases M.cut i y <;> cases M.cut i z <;> norm_num [sep]

lemma Model.pullback_dist {X : Type u} {Y : Type v} (M : Model X) (f : Y → X) (x y : Y) :
    (M.pullback f).dist x y = M.dist (f x) (f y) := rfl

lemma Model.scale_dist {X : Type u} (M : Model X) (a : ℝ) (ha : 0 ≤ a) (x y : X) :
    (M.scale a ha).dist x y = a*M.dist x y := by
  simp only [Model.dist,Model.scale,mul_assoc,mul_sum]
  rfl

lemma Model.total_dist {X : Type u} {J : Type} [Fintype J] (M : J → Model X) (x y : X) :
    (Model.total M).dist x y = ∑ j, (M j).dist x y := by
  change (∑ i : (j : J) × (M j).Index, (M i.1).weight i.2 * sep ((M i.1).cut i.2 x) ((M i.1).cut i.2 y)) = _
  rw [Fintype.sum_sigma]
  rfl

lemma initial_cut_sum {s a : ℕ} (ha : a ≤ s) :
    (∑ t : Fin s, if t.val < a then (1 : ℝ) else 0) = (a : ℝ) := by
  simp only [sum_boole,Fin.card_filter_val_lt,min_eq_right ha]

theorem threshold_sum {s a b : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    (∑ t : Fin s, sep (decide (t.val < a)) (decide (t.val < b))) = |(a : ℝ)-(b : ℝ)| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm]
    calc
      _ = ∑ t : Fin s, sep (decide (t.val < b)) (decide (t.val < a)) := by
        apply sum_congr rfl
        intro t _
        simp only [sep,eq_comm]
      _ = _ := this hb ha (by omega)
  have he (t : Fin s) : sep (decide (t.val < a)) (decide (t.val < b)) =
      (if t.val < b then (1 : ℝ) else 0)-(if t.val < a then (1 : ℝ) else 0) := by
    by_cases hta : t.val < a <;> by_cases htb : t.val < b <;> simp [sep,hta,htb]; omega
  simp_rw [he]
  rw [sum_sub_distrib,initial_cut_sum hb,initial_cut_sum ha,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hab))]
  ring

end EditCutModel

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

lemma count_cast {J K : Type*} [Fintype J] (f : J → K) (z : K) :
    (countNat f z : ℝ) = EditCutHash.count f z := by
  simp only [countNat,EditCutHash.count,EditCutHash.hit,sum_boole]

lemma count_bound {J K : Type*} [Fintype J] (f : J → K) (z : K) :
    countNat f z ≤ Fintype.card J := card_filter_le _ _

lemma Model.histogram_dist {X : Type*} (M : Model X) (s : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (f g : Fin s → X) :
    (M.histogram s a ha).dist f g = EditCutHash.meanHistogram M.weight a M.cut f g := by
  change (∑ i : (M.Index → Bool) × (M.Index → Bool) × Fin s,
    EditCutHash.probability M.weight a i.1 * sep
      (decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (f j)) i.2.1))
      (decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (g j)) i.2.1))) = _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro h _
  rw [Fintype.sum_prod_type]
  simp_rw [←mul_sum]
  congr 1
  apply sum_congr rfl
  intro z _
  rw [threshold_sum (by simpa using count_bound (fun j => EditCutHash.key M.cut h (f j)) z)
    (by simpa using count_bound (fun j => EditCutHash.key M.cut h (g j)) z),count_cast,count_cast]

lemma Model.distance_eq {X : Type*} (M : Model X) (x y : X) :
    EditCutHash.distance M.weight M.cut x y = M.dist x y := by
  unfold EditCutHash.distance Model.dist
  apply sum_congr rfl
  intro i _
  congr 1
  cases M.cut i x <;> cases M.cut i y <;> norm_num [sep,EditCutHash.sep]

end EditCutModel

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_CutRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Realization of all finite-cut distances by one summable vector map
-/

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

lemma singleton_sub_norm (a b : ℝ) :
    ‖lp.single (E := fun _ : ℕ => ℝ) 1 0 a - lp.single (E := fun _ : ℕ => ℝ) 1 0 b‖ = |a-b| := by
  have he : lp.single (E := fun _ : ℕ => ℝ) 1 0 a - lp.single (E := fun _ : ℕ => ℝ) 1 0 b =
      lp.single (E := fun _ : ℕ => ℝ) 1 0 (a-b) := by
    ext i
    change (lp.single (E := fun _ : ℕ => ℝ) 1 0 a) i - (lp.single (E := fun _ : ℕ => ℝ) 1 0 b) i = (lp.single (E := fun _ : ℕ => ℝ) 1 0 (a-b)) i
    by_cases hi : i = 0
    · subst i
      simp only [lp.single_apply_self]
    · rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 a hi,
        lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 b hi,
        lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 (a-b) hi,sub_self]
  rw [he,lp.norm_single (by norm_num)]
  exact Real.norm_eq_abs _

lemma Model.vector_distance {X : Type*} (M : Model X) (x y : X) :
    ‖M.vector x-M.vector y‖ = M.dist x y := by
  unfold Model.vector
  rw [EditL1.pack_distance,Fintype.sum_option]
  simp only [sub_self,norm_zero,zero_add]
  unfold Model.dist
  apply sum_congr rfl
  intro i _
  rw [singleton_sub_norm]
  cases hix : M.cut i x <;> cases hiy : M.cut i y <;>
    simp [sep, abs_of_nonneg (M.nonneg i)]

end EditCutModel

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_DyadicScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic scales for window displacement
-/

namespace EditDyadic

lemma log_mono {a b : ℕ} (hab : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := by
  exact Nat.log_mono_right hab

lemma scale {l delta : ℕ} (hl : 0 < l) (hd : 0 < delta) (hdl : delta ≤ 2*l) :
    ∃ j : Fin (Nat.log 2 l+1),
      let s := 2^j.val
      1 ≤ s ∧ s ≤ l ∧ delta ≤ 16*s ∧ 2*(s-1)+s ≤ delta := by
  by_cases hsmall : delta < 4
  · refine ⟨⟨0,by omega⟩,?_⟩
    simp only [pow_zero]
    omega
  · let m := delta/4
    have hm : 0 < m := by dsimp [m]; omega
    have hml : m ≤ l := by dsimp [m]; omega
    have hj : Nat.log 2 m < Nat.log 2 l+1 := by have := log_mono hml; omega
    refine ⟨⟨Nat.log 2 m,hj⟩,?_⟩
    dsimp only
    have hs : 1 ≤ 2^Nat.log 2 m := Nat.one_le_pow _ _ (by omega)
    have hsm : 2^Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have hm2 := Nat.lt_pow_succ_log_self (by omega : 1 < 2) m
    rw [pow_succ] at hm2
    dsimp [m] at *
    refine ⟨hs,hsm.trans hml,?_,?_⟩ <;> omega

lemma scale_le {l : ℕ} (hl : 0 < l) (j : Fin (Nat.log 2 l+1)) : 2^j.val ≤ l := by
  exact (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : j.val ≤ Nat.log 2 l)).trans
    (Nat.pow_log_le_self 2 (by omega))

end EditDyadic

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Padded windows and insertion-deletion matching inequalities
-/

namespace EditWindow
open EditDistortion

variable {A : Type*}

lemma lookup_insert_before (p q : List A) (a : A) {r : ℕ} (hr : r < p.length) :
    (p ++ a::q)[r]? = (p ++ q)[r]? := by
  rw [List.getElem?_append_left hr,List.getElem?_append_left hr]

lemma lookup_insert_after (p q : List A) (a : A) {r : ℕ} (hr : p.length ≤ r) :
    (p ++ a::q)[r+1]? = (p ++ q)[r]? := by
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right hr]
  have he : r+1-p.length = (r-p.length)+1 := by omega
  simp only [he,List.getElem?_cons_succ]

lemma window_before (p q : List A) (a : A) {start len : ℕ} (h : start+len ≤ p.length) :
    window (p ++ a::q) start len = window (p ++ q) start len := by
  unfold window
  congr 1
  funext i
  exact lookup_insert_before p q a (by omega)

lemma window_after (p q : List A) (a : A) {start len : ℕ} (h : p.length ≤ start) :
    window (p ++ a::q) (start+1) len = window (p ++ q) start len := by
  unfold window
  congr 1
  funext i
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
    lookup_insert_after p q a (r := start+i.val) (by omega)

theorem window_insert_cost (p q : List A) (a : A) (start len : ℕ) :
    indel (window (p ++ q) start len) (window (p ++ a::q) start len) ≤ 2 := by
  by_cases hl : len = 0
  · subst len
    have hh : indel ([] : List (Option A)) [] = 0 := (cost_eq_zero_iff (s := false)).mpr rfl
    simpa only [window,List.ofFn_zero,hh] using (by norm_num : (0 : ℕ) ≤ 2)
  have hlp : 0 < len := Nat.pos_of_ne_zero hl
  let f : Fin (len-1) ↪o Fin len :=
    (Fin.castLEOrderEmb (by omega : len-1 ≤ len))
  let g₀ (i : Fin (len-1)) : Fin len :=
    ⟨if start+i.val < p.length then i.val else i.val+1,by split <;> omega⟩
  have hg : StrictMono g₀ := by
    intro i j hij
    have hij' : i.val < j.val := hij
    change (if start+i.val < p.length then i.val else i.val+1) <
      (if start+j.val < p.length then j.val else j.val+1)
    split <;> split <;> omega
  let g : Fin (len-1) ↪o Fin len := OrderEmbedding.ofStrictMono g₀ hg
  have he (i : Fin (len-1)) :
      (p ++ q)[start+(f i).val]? = (p ++ a::q)[start+(g i).val]? := by
    change (p ++ q)[start+i.val]? =
      (p ++ a::q)[start+(if start+i.val < p.length then i.val else i.val+1)]?
    split
    · rename_i hi
      exact (lookup_insert_before p q a hi).symm
    · rename_i hi
      simpa only [Nat.add_assoc] using
        (lookup_insert_after p q a (r := start+i.val) (by omega)).symm
  have hh := indel_le_of_matching (fun i : Fin len => (p ++ q)[start+i.val]?)
    (fun i : Fin len => (p ++ a::q)[start+i.val]?) f g he
  exact hh.trans (by omega)

end EditWindow

namespace EditDistortion
variable {A B : Type*}

lemma indel_cost (x y : List A) : indel x y = cost false x y := rfl

lemma step_indel_filterMap (f : A → Option B) {x y : List A} (h : Step false x y) :
    indel (x.filterMap f) (y.filterMap f) ≤ 1 := by
  cases h with
  | insert p q a =>
    cases ha : f a with
    | none => simp only [List.filterMap_append,List.filterMap_cons,ha,indel_cost,cost_refl]; omega
    | some b =>
      simpa only [List.filterMap_append,List.filterMap_cons,ha,indel_cost] using
        cost_le (Script.single (Step.insert (substitutions := false) (p.filterMap f) (q.filterMap f) b))
  | delete p q a =>
    cases ha : f a with
    | none => simp only [List.filterMap_append,List.filterMap_cons,ha,indel_cost,cost_refl]; omega
    | some b =>
      simpa only [List.filterMap_append,List.filterMap_cons,ha,indel_cost] using
        cost_le (Script.single (Step.delete (substitutions := false) (p.filterMap f) (q.filterMap f) b))
  | substitute hf => contradiction

lemma indel_filterMap_le (f : A → Option B) (x y : List A) :
    indel (x.filterMap f) (y.filterMap f) ≤ indel x y := by
  have hh {n : ℕ} {x y : List A} (h : Script false n x y) :
      indel (x.filterMap f) (y.filterMap f) ≤ n := by
    induction h with
    | nil x => exact cost_le (.nil _)
    | @cons n x y z e h ih =>
      have ht := cost_triangle (s := false) (x.filterMap f) (y.filterMap f) (z.filterMap f)
      have he := step_indel_filterMap f e
      rw [indel_cost] at he ih ⊢
      omega
  exact hh (cost_spec x y)
end EditDistortion

namespace EditWindow
open EditDistortion
variable {A : Type*}

lemma segment_sublist (x : ℕ → A) (start l k L : ℕ) (hk : k+L ≤ l) :
    (segment x (start+k) L).Sublist (segment x start l) := by
  let f : Fin L ↪o Fin l := OrderEmbedding.ofStrictMono
    (fun i => (⟨k+i.val,by omega⟩ : Fin l)) (by intro i j hij; change k+i.val < k+j.val; omega)
  have hh := sublist_ofFn_comp (fun i : Fin l => x (start+i.val)) f
  dsimp [f,OrderEmbedding.ofStrictMono] at hh
  simpa only [segment,Nat.add_assoc] using hh

lemma segment_loss (x : ℕ → A) (start l k L : ℕ) (hk : k+L ≤ l) :
    indel (segment x start l) (segment x (start+k) L) ≤ l-L := by
  simpa only [segment_length,indel_cost] using cost_le (Script.of_sublist (segment_sublist x start l k L hk))

lemma segment_cross (x y : ℕ → A) (start l s : ℕ) (hs : 1 ≤ s) (hsl : s ≤ l)
    (i j : Fin s) :
    indel (segment x start l) (segment y start l) ≤
      2*(s-1)+indel (segment x (start+i.val) (l-s+1)) (segment y (start+j.val) (l-s+1)) := by
  have hx := segment_loss x start l i.val (l-s+1) (by omega)
  have hy := segment_loss y start l j.val (l-s+1) (by omega)
  rw [indel_cost,cost_symm] at hy
  have h1 := cost_triangle (s := false) (segment x start l)
    (segment x (start+i.val) (l-s+1)) (segment y (start+j.val) (l-s+1))
  have h2 := cost_triangle (s := false) (segment x start l)
    (segment y (start+j.val) (l-s+1)) (segment y start l)
  simp only [indel_cost] at hx hy ⊢
  omega

lemma segment_append (x : ℕ → A) (start l m : ℕ) :
    segment x start (l+m) = segment x start l ++ segment x (start+l) m := by
  unfold segment
  rw [List.ofFn_add]
  congr 1
  congr 1
  funext i
  simp only [Fin.val_natAdd,Nat.add_assoc]

lemma indel_segment_blocks (x y : ℕ → A) (l b : ℕ) :
    indel (segment x 0 (b*l)) (segment y 0 (b*l)) ≤
      ∑ j ∈ Finset.range b, indel (segment x (j*l) l) (segment y (j*l) l) := by
  induction b with
  | zero => simp only [Nat.zero_mul,segment,List.ofFn_zero,Finset.sum_range_zero]; exact cost_le (.nil _)
  | succ b ih =>
    rw [Nat.succ_mul,segment_append,segment_append,Finset.sum_range_succ]
    simp only [Nat.zero_add]
    exact (cost_append_le (s := false) _ _ _ _).trans (Nat.add_le_add_right ih _)

lemma window_padding (x : List A) (n : ℕ) (hx : x.length ≤ n) :
    window x 0 n = (x.map some) ++ List.replicate (n-x.length) none := by
  apply List.ext_getElem?
  intro i
  simp only [window,List.getElem?_ofFn,Nat.zero_add,List.getElem?_append,List.length_map,
    List.getElem?_map,List.getElem?_replicate]
  by_cases hix : i < x.length
  · have hin : i < n := lt_of_lt_of_le hix hx
    simp [hix,hin]
  · have hxn : x[i]? = none := List.getElem?_eq_none (by omega)
    have hi : i-x.length < n-x.length ↔ i < n := by omega
    simp only [ite_eq_right hix,hxn,hi]
    split <;> rfl

lemma filterMap_window (x : List A) (n : ℕ) (hx : x.length ≤ n) :
    (window x 0 n).filterMap id = x := by
  rw [window_padding x n hx]
  simp

lemma indel_le_window (x y : List A) (n : ℕ) (hx : x.length ≤ n) (hy : y.length ≤ n) :
    indel x y ≤ indel (window x 0 n) (window y 0 n) := by
  have hh := indel_filterMap_le id (window x 0 n) (window y 0 n)
  simpa only [filterMap_window x n hx,filterMap_window y n hy] using hh

end EditWindow

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_WindowRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic-window recursion and insertion bounds
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

variable {A : Type*}

lemma piece_nonneg (M : Model (List (Option A))) (x y : List A) (start l s : ℕ) (hs : 0 < s) :
    0 ≤ piece M x y start l s :=
  EditCutHash.meanHistogram_nonneg M.nonneg (EditCutHash.rate_nonneg hs) _ _ _

lemma lift_dist (M : Model (List (Option A))) (b l : ℕ) (x y : List A) :
    (lift M b l).dist x y =
      16 * ∑ j : Fin b, ∑ r : Fin (Nat.log 2 l+1), piece M x y (j.val*l) l (2^r.val) := by
  rw [lift,Model.scale_dist,Model.total_dist,Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro r _
  rw [Model.pullback_dist,Model.histogram_dist]
  rfl

lemma block_indel_bound (x y : List A) (start l : ℕ) :
    indel (window x start l) (window y start l) ≤ 2*l := by
  have h : indel (window x start l) (window y start l) ≤
      (window x start l).length+(window y start l).length := by
    exact cost_le ((Script.to_nil (s := false) _).trans (Script.to_nil _).symm)
  simpa only [window_length,two_mul] using h

lemma block_lower (M : Model (List (Option A))) (l : ℕ) (hl : 0 < l)
    (hM : ∀ u v : List (Option A), u.length ≤ l → v.length ≤ l →
      (indel u v : ℝ) ≤ M.dist u v) (x y : List A) (start : ℕ) :
    (indel (window x start l) (window y start l) : ℝ) ≤
      16 * ∑ r : Fin (Nat.log 2 l+1), piece M x y start l (2^r.val) := by
  let delta := indel (window x start l) (window y start l)
  have hnn (r : Fin (Nat.log 2 l+1)) : 0 ≤ piece M x y start l (2^r.val) :=
    piece_nonneg _ _ _ _ _ _ (pow_pos (by omega) _)
  by_cases hd : delta = 0
  · change (delta : ℝ) ≤ _
    rw [hd,Nat.cast_zero]
    exact mul_nonneg (by norm_num) (sum_nonneg (fun r _ => hnn r))
  · obtain ⟨r,hs,hsl,hds,hsd⟩ := EditDyadic.scale hl (Nat.pos_of_ne_zero hd) (block_indel_bound x y start l)
    have hcross (i j : Fin (2^r.val)) : ((2^r.val : ℕ) : ℝ) ≤
        EditCutHash.distance M.weight M.cut (samples x start l (2^r.val) i) (samples y start l (2^r.val) j) := by
      rw [Model.distance_eq]
      have htri := segment_cross (fun k => x[k]?) (fun k => y[k]?) start l (2^r.val) hs hsl i j
      change delta ≤ 2*(2^r.val-1)+indel (samples x start l (2^r.val) i)
        (samples y start l (2^r.val) j) at htri
      have hloss : 2^r.val ≤ indel (samples x start l (2^r.val) i)
          (samples y start l (2^r.val) j) := by omega
      calc
        _ ≤ (indel (samples x start l (2^r.val) i) (samples y start l (2^r.val) j) : ℝ) := by exact_mod_cast hloss
        _ ≤ _ := hM _ _ (by simp only [samples,window_length]; omega) (by simp only [samples,window_length]; omega)
    have hh := EditCutHash.meanHistogram_separated (by omega : 0 < 2^r.val) M.nonneg M.cut
      (samples x start l (2^r.val)) (samples y start l (2^r.val)) hcross
    change ((2^r.val : ℕ) : ℝ) ≤ piece M x y start l (2^r.val) at hh
    have hsum := single_le_sum (fun j _ => hnn j) (mem_univ r)
    have hdsr : (delta : ℝ) ≤ 16*((2^r.val : ℕ) : ℝ) := by exact_mod_cast hds
    change (delta : ℝ) ≤ _
    nlinarith

lemma lift_lower (M : Model (List (Option A))) (b l : ℕ) (hl : 0 < l)
    (hM : ∀ u v : List (Option A), u.length ≤ l → v.length ≤ l →
      (indel u v : ℝ) ≤ M.dist u v) (x y : List A)
    (hx : x.length ≤ b*l) (hy : y.length ≤ b*l) :
    (indel x y : ℝ) ≤ (lift M b l).dist x y := by
  have h1 := indel_le_window x y (b*l) hx hy
  have h2 := indel_segment_blocks (fun k => x[k]?) (fun k => y[k]?) l b
  change indel (window x 0 (b*l)) (window y 0 (b*l)) ≤ _ at h2
  have h3 : (indel x y : ℝ) ≤
      ∑ j : Fin b, (indel (window x (j.val*l) l) (window y (j.val*l) l) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (indel (window x (j*l) l) (window y (j*l) l) : ℝ)) b]
    exact_mod_cast h1.trans h2
  rw [lift_dist,mul_sum]
  apply h3.trans
  apply sum_le_sum
  intro j _
  exact block_lower M l hl hM x y (j.val*l)

lemma piece_insert_general (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (start l s : ℕ) (hs : 0 < s) :
    piece M (p++q) (p++a::q) start l s ≤ 4*Real.log (2*(s : ℝ)^2)*D := by
  have hup := EditCutHash.meanHistogram_upper M.nonneg (EditCutHash.rate_nonneg hs) M.cut
    (samples (p++q) start l s) (samples (p++a::q) start l s)
  have hsum : (∑ i : Fin s, EditCutHash.distance M.weight M.cut
      (samples (p++q) start l s i) (samples (p++a::q) start l s i)) ≤ (s : ℝ)*(2*D) := by
    calc
      _ ≤ ∑ _i : Fin s, 2*D := by
        apply sum_le_sum
        intro i _
        rw [Model.distance_eq]
        have hcost := window_insert_cost p q a (start+i.val) (l-s+1)
        have hcr : (indel (samples (p++q) start l s i) (samples (p++a::q) start l s i) : ℝ) ≤ 2 := by exact_mod_cast hcost
        exact (hM _ _).trans (by nlinarith)
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hr := EditCutHash.rate_nonneg hs
  have h := hup.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  change piece M (p++q) (p++a::q) start l s ≤ _ at h
  apply h.trans_eq
  unfold EditCutHash.rate
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  field_simp
  ring

lemma piece_before (M : Model (List (Option A))) (p q : List A) (a : A)
    (start l s : ℕ) (_hs : 0 < s) (hsl : s ≤ l) (hp : start+l ≤ p.length) :
    piece M (p++q) (p++a::q) start l s = 0 := by
  have he : samples (p++q) start l s = samples (p++a::q) start l s := by
    funext i
    exact (window_before p q a (by omega)).symm
  unfold piece
  rw [←he,EditCutHash.meanHistogram_self]

lemma piece_after (M : Model (List (Option A))) (p q : List A) (a : A)
    (start l s : ℕ) (hs : 0 < s) (hp : p.length ≤ start) :
    piece M (p++q) (p++a::q) start l s ≤ 2 := by
  apply EditCutHash.meanHistogram_shift hs M.nonneg (EditCutHash.rate_nonneg hs)
  intro i
  exact (window_after p q a (by omega)).symm

end EditUpper

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel
variable {A : Type*}

lemma sum_block_insert (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (b l s : ℕ) (hl : 0 < l) (hs : 0 < s) (hsl : s ≤ l) :
    (∑ j : Fin b, piece M (p++q) (p++a::q) (j.val*l) l s) ≤
      2*(b : ℝ)+4*Real.log (2*(s : ℝ)^2)*D := by
  let K := 4*Real.log (2*(s : ℝ)^2)*D
  have hK : 0 ≤ K := by
    dsimp [K]
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith))) hD
  have hj (j : Fin b) : piece M (p++q) (p++a::q) (j.val*l) l s ≤
      2+(if j.val = p.length/l then K else 0) := by
    by_cases he : j.val = p.length/l
    · rw [ite_eq_left he]
      have hh := piece_insert_general M hD hM p q a (j.val*l) l s hs
      change _ ≤ K at hh
      linarith
    · rw [ite_eq_right he,add_zero]
      by_cases hlt : j.val < p.length/l
      · have hp : j.val*l+l ≤ p.length := by
          have h1 := Nat.mul_le_mul_right l (show j.val+1 ≤ p.length/l by omega)
          have h2 := Nat.div_mul_le_self p.length l
          nlinarith
        rw [piece_before M p q a (j.val*l) l s hs hsl hp]
        norm_num
      · have hp : p.length ≤ j.val*l := by
          have h1 := Nat.mul_le_mul_right l (show p.length/l+1 ≤ j.val by omega)
          have h2 := Nat.lt_mul_div_succ p.length hl
          nlinarith
        exact piece_after M p q a (j.val*l) l s hs hp
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin b))) => hj j)
  rw [sum_add_distrib] at hsum
  have hc : (∑ j : Fin b, (if j.val = p.length/l then K else 0)) ≤ K := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = p.length/l then K else 0) b,sum_ite_eq']
    split <;> linarith
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  dsimp [K] at hc hsum
  linarith

lemma lift_insert_raw (M : Model (List (Option A))) {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ u v, M.dist u v ≤ D*(indel u v : ℝ))
    (p q : List A) (a : A) (b l : ℕ) (hl : 0 < l) :
    (lift M b l).dist (p++q) (p++a::q) ≤
      16*(Nat.log 2 l+1 : ℕ)*(2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) := by
  rw [lift_dist,sum_comm]
  have hscale (r : Fin (Nat.log 2 l+1)) : (∑ j : Fin b,
      piece M (p++q) (p++a::q) (j.val*l) l (2^r.val)) ≤
      2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D := by
    have hr := EditDyadic.scale_le hl r
    have hp : 0 < 2^r.val := pow_pos (by omega) _
    have h := sum_block_insert M hD hM p q a b l (2^r.val) hl hp hr
    apply h.trans
    have hrr : ((2^r.val : ℕ) : ℝ) ≤ l := by exact_mod_cast hr
    have hlog : Real.log (2*(((2^r.val : ℕ) : ℝ))^2) ≤ Real.log (2*(l : ℝ)^2) := by
      apply Real.log_le_log (by positivity)
      gcongr
    nlinarith
  calc
    _ ≤ 16 * ∑ _r : Fin (Nat.log 2 l+1), (2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hscale r)) (by norm_num)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma model_indel_lipschitz (M : Model (List A)) {D : ℝ}
    (hstep : ∀ (p q : List A) (a : A), M.dist (p++q) (p++a::q) ≤ D) :
    ∀ x y, M.dist x y ≤ D*(indel x y : ℝ) := by
  have he {x y : List A} (h : Step false x y) : M.dist x y ≤ D := by
    cases h with
    | insert p q a => exact hstep p q a
    | delete p q a => rw [Model.dist_symm]; exact hstep p q a
    | substitute h => contradiction
  have hs {n : ℕ} {x y : List A} (h : Script false n x y) : M.dist x y ≤ D*(n : ℝ) := by
    induction h with
    | nil x => simp
    | @cons n x y z e h ih =>
      have ht := M.dist_triangle x y z
      have hh := he e
      push_cast
      nlinarith
  intro x y
  exact hs (cost_spec x y)

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Base finite-cut embedding for short words
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel
variable {A : Type*} [Fintype A]

lemma base_distance (x y : List A) :
    (base (A := A)).dist x y = 2*EditCutHash.sep (x[0]?) (y[0]?) := by
  have hcuts (i : Fin (Fintype.card (Option A))) :
      sep (decide (firstKey x = i)) (decide (firstKey y = i)) =
        |EditCutHash.hit (firstKey x) i-EditCutHash.hit (firstKey y) i| := by
    by_cases hx : firstKey x = i <;> by_cases hy : firstKey y = i <;>
      simp [sep,EditCutHash.hit,hx,hy]
  change (∑ i, 1*sep (decide (firstKey x = i)) (decide (firstKey y = i))) = _
  simp_rw [one_mul,hcuts]
  rw [EditCutHash.hit_distance]
  congr 1
  have he : firstKey x = firstKey y ↔ x[0]? = y[0]? := (Fintype.equivFin (Option A)).injective.eq_iff
  by_cases hxy : x[0]? = y[0]? <;> simp only [EditCutHash.sep,he,hxy,ite_true,ite_false]

lemma base_le_two (x y : List A) : (base (A := A)).dist x y ≤ 2 := by
  rw [base_distance]
  have h := EditCutHash.sep_le_one (x[0]?) (y[0]?)
  linarith

omit [Fintype A] in
lemma first_eq_of_small (x y : List A) (hx : x.length ≤ 1) (hy : y.length ≤ 1)
    (he : x[0]? = y[0]?) : x = y := by
  cases x with
  | nil => cases y <;> simp_all
  | cons a x =>
    have hxn : x = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hx; omega)
    subst x
    cases y with
    | nil => simp at he
    | cons b y =>
      have hyn : y = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hy; omega)
      subst y
      simpa using he

lemma base_lower (x y : List A) (hx : x.length ≤ 1) (hy : y.length ≤ 1) :
    (indel x y : ℝ) ≤ (base (A := A)).dist x y := by
  by_cases he : x[0]? = y[0]?
  · have hxy := first_eq_of_small x y hx hy he
    subst y
    rw [Model.dist_self]
    norm_cast
    exact cost_le (.nil _)
  · rw [base_distance,EditCutHash.sep_eq_one he,mul_one]
    have hlen : indel x y ≤ x.length+y.length :=
      cost_le ((Script.to_nil (s := false) x).trans (Script.to_nil y).symm)
    exact_mod_cast (show indel x y ≤ 2 by omega)

lemma base_upper (x y : List A) : (base (A := A)).dist x y ≤ 2*(indel x y : ℝ) :=
  model_indel_lipschitz base (fun p q a => base_le_two (p++q) (p++a::q)) x y

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform finite-cut embeddings at recursive capacities
-/

namespace EditUpperParameters
open scoped BigOperators

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh

lemma scale_count_bound {l : ℕ} (hl : 0 < l) :
    ((Nat.log 2 l+1 : ℕ) : ℝ) ≤ 2*(1+Real.log (l : ℝ)) := by
  have hpow := Nat.pow_log_le_self 2 (Nat.ne_of_gt hl)
  have hpr : (2 : ℝ)^(Nat.log 2 l) ≤ l := by exact_mod_cast hpow
  have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hpr
  rw [Real.log_pow] at hh
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hl)
  have hm : 0 ≤ (Nat.log 2 l : ℝ) := Nat.cast_nonneg _
  have h2 := log_two_bounds
  push_cast
  nlinarith

lemma log_square_bound {l : ℕ} (hl : 0 < l) :
    Real.log (2*(l : ℝ)^2) ≤ 2*(1+Real.log (l : ℝ)) := by
  have hp : (0 : ℝ)<l := by exact_mod_cast hl
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hp.ne'),Real.log_pow]
  have h2 := log_two_bounds
  norm_num only [Nat.cast_ofNat]
  linarith

lemma step_constant_bound {b l : ℕ} (hl : 0 < l) {D : ℝ} (hD : 0 ≤ D) :
    16*((Nat.log 2 l+1 : ℕ) : ℝ)*(2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) ≤
      512*(1+Real.log (l : ℝ))^2*((b : ℝ)+D) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hl)
  have hcount := scale_count_bound hl
  have hsq := log_square_bound hl
  have hsnn : 0 ≤ Real.log (2*(l : ℝ)^2) := Real.log_nonneg (by
    have hh : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith)
  have hb := Nat.cast_nonneg (α := ℝ) b
  have hm := Nat.cast_nonneg (α := ℝ) (Nat.log 2 l+1)
  have hleft : 2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D ≤ 2*b+8*(1+Real.log (l : ℝ))*D := by nlinarith
  calc
    _ ≤ 16*(2*(1+Real.log (l : ℝ)))*(2*b+8*(1+Real.log (l : ℝ))*D) := by
      apply mul_le_mul
      · nlinarith
      · exact hleft
      · positivity
      · positivity
    _ ≤ _ := by nlinarith [mul_nonneg hlog hb,mul_nonneg (sq_nonneg (1+Real.log (l : ℝ))) hD,
        mul_nonneg (sq_nonneg (Real.log (l : ℝ))) hb]

end EditUpperParameters

namespace EditUpper

universe u

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

lemma growth_ge {b N : ℕ} (hb : 1 ≤ b) : 1 ≤ growth b N := by
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  have hn := Nat.cast_nonneg (α := ℝ) N
  dsimp [growth]
  nlinarith [mul_nonneg hn hlog]

theorem exists_level (b N : ℕ) (hb : 1 ≤ b) (k : ℕ) (hk : k ≤ N)
    (A : Type u) [Fintype A] :
    ∃ M : Model (List A),
      (∀ x y : List A, x.length ≤ b^k → y.length ≤ b^k → (indel x y : ℝ) ≤ M.dist x y) ∧
      (∀ x y : List A, M.dist x y ≤ ((b : ℝ)+2)*(growth b N)^k*(indel x y : ℝ)) := by
  induction k generalizing A with
  | zero =>
    refine ⟨base,?_,?_⟩
    · intro x y hx hy
      exact base_lower x y (by simpa using hx) (by simpa using hy)
    · intro x y
      have hh := base_upper x y
      have hi := Nat.cast_nonneg (α := ℝ) (indel x y)
      simp only [pow_zero,mul_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) b]
  | succ k ih =>
    obtain ⟨M,hlo,hup⟩ := ih (by omega) (Option A)
    let D := ((b : ℝ)+2)*(growth b N)^k
    have hP := growth_ge (N := N) hb
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hpow : 1 ≤ (growth b N)^k := one_le_pow₀ hP
    have hbD : (b : ℝ) ≤ D := by
      dsimp [D]
      have hb0 := Nat.cast_nonneg (α := ℝ) b
      nlinarith
    have hl : 0 < b^k := pow_pos (by omega) _
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
    have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb)
    have hT : 1+Real.log ((b^k : ℕ) : ℝ) ≤ 1+(N : ℝ)*Real.log (b : ℝ) := by
      rw [Nat.cast_pow,Real.log_pow]
      nlinarith
    have hTnn : 0 ≤ 1+Real.log ((b^k : ℕ) : ℝ) := by
      have hh : 0 ≤ Real.log ((b^k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.one_le_pow k b (by omega)))
      linarith
    have hconst : 512*(1+Real.log ((b^k : ℕ) : ℝ))^2*((b : ℝ)+D) ≤
        ((b : ℝ)+2)*(growth b N)^(k+1) := by
      calc
        _ ≤ 512*(1+(N : ℝ)*Real.log (b : ℝ))^2*(2*D) := by
          apply mul_le_mul
          · gcongr
          · linarith
          · positivity
          · positivity
        _ = _ := by dsimp [D,growth]; rw [pow_succ]; ring
    refine ⟨lift M b (b^k),?_,?_⟩
    · intro x y hx hy
      apply lift_lower M b (b^k) hl hlo x y
      · simpa only [pow_succ,Nat.mul_comm] using hx
      · simpa only [pow_succ,Nat.mul_comm] using hy
    · apply model_indel_lipschitz
      intro p q a
      exact (lift_insert_raw M hD hup p q a b (b^k) hl).trans
        ((EditUpperParameters.step_constant_bound hl hD).trans hconst)

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Branching and depth choices at every sufficiently large length
-/

namespace EditUpperParameters
open Filter

lemma radius_peak {t : ℝ} (ht : 1 ≤ t) (hlt : 1 ≤ Real.log t) :
    EditDepth.radius t * Real.log t = peak t ∧ EditDepth.radius t * peak t = t ∧ 1 ≤ peak t := by
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have hr : 0 ≤ EditDepth.radius t := EditDepth.radius_nonneg t
  have hr2 : EditDepth.radius t^2 = t/Real.log t := Real.sq_sqrt (div_nonneg tp.le lp.le)
  have hr2' : EditDepth.radius t^2*Real.log t = t := (eq_div_iff lp.ne').mp hr2
  have hs : peak t = EditDepth.radius t*Real.log t := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log t) hr2']
  refine ⟨hs.symm,?_,?_⟩
  · rw [hs]
    nlinarith [hr2']
  · apply Real.le_sqrt_of_sq_le
    nlinarith

lemma choose_parameters {t : ℝ} (ht : 1 ≤ t) (hlt : 1024 ≤ Real.log t)
    (hr : 2 ≤ EditDepth.radius t) :
    1 ≤ level t ∧ 2 ≤ branching t ∧
      Real.exp t ≤ (branching t : ℝ)^(level t) ∧
      2*((branching t : ℝ)+2)*
        (1024*(1+(level t : ℝ)*Real.log (branching t : ℝ))^2)^(level t) ≤
          Real.exp (32*peak t) := by
  have hlt1 : 1 ≤ Real.log t := by linarith
  obtain ⟨hRS,hRt,hS⟩ := radius_peak ht hlt1
  have hNup : (level t : ℝ) ≤ EditDepth.radius t := Nat.floor_le (EditDepth.radius_nonneg t)
  have hNfloor := Nat.lt_floor_add_one (EditDepth.radius t)
  change EditDepth.radius t < (level t : ℝ)+1 at hNfloor
  have hNlo : EditDepth.radius t/2 ≤ (level t : ℝ) := by linarith
  have hNp : 1 ≤ level t := by
    have hh : (1 : ℝ) ≤ level t := by linarith
    exact_mod_cast hh
  have helo : Real.exp (2*peak t) ≤ (branching t : ℝ) := Nat.le_ceil _
  have hehi : (branching t : ℝ) < Real.exp (2*peak t)+1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hexp : 3 ≤ Real.exp (2*peak t) := by have := Real.add_one_le_exp (2*peak t); linarith
  have hb : 2 ≤ branching t := by
    have hh : (2 : ℝ) ≤ branching t := by linarith
    exact_mod_cast hh
  have hbp : (0 : ℝ) < branching t := by exact_mod_cast (show 0 < branching t by omega)
  have hBnon : 0 ≤ Real.log (branching t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ branching t by omega))
  have hBlo : 2*peak t ≤ Real.log (branching t : ℝ) := (Real.le_log_iff_exp_le hbp).mpr helo
  have hBup : Real.log (branching t : ℝ) ≤ 3*peak t := by
    have hh : (branching t : ℝ) ≤ 2*Real.exp (2*peak t) := by linarith
    have hl := Real.log_le_log hbp hh
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hl
    have h2 := log_two_bounds
    linarith
  have hBlog : Real.log ((branching t : ℝ)+2) ≤ 5*peak t := by
    have hh : (branching t : ℝ)+2 ≤ 4*Real.exp (2*peak t) := by linarith
    have hl := Real.log_le_log (by positivity : 0 < (branching t : ℝ)+2) hh
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hl
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
    linarith
  have hNnon : 0 ≤ (level t : ℝ) := Nat.cast_nonneg _
  have hNblo : t ≤ (level t : ℝ)*Real.log (branching t : ℝ) := by
    have hh := mul_le_mul hNlo hBlo (by linarith : 0 ≤ 2*peak t) hNnon
    nlinarith [hRt]
  have hNbup : (level t : ℝ)*Real.log (branching t : ℝ) ≤ 3*t := by
    have hh := mul_le_mul hNup hBup hBnon (EditDepth.radius_nonneg t)
    nlinarith [hRt]
  have hcap : Real.exp t ≤ (branching t : ℝ)^(level t) := by
    apply (Real.le_log_iff_exp_le (pow_pos hbp _)).mp
    rw [Real.log_pow]
    exact hNblo
  let T := 1+(level t : ℝ)*Real.log (branching t : ℝ)
  let P := 1024*T^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hTup : T ≤ 4*t := by dsimp [T]; linarith
  have hlogT : Real.log T ≤ 3+Real.log t := by
    have hh := Real.log_le_log hT hTup
    rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at hh
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
    linarith
  have hlogP : Real.log P ≤ 4*Real.log t := by
    dsimp [P]
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hT.ne'),Real.log_pow]
    have h1024 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<1024)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hNP : (level t : ℝ)*Real.log P ≤ 4*peak t := by
    have h1 := mul_le_mul_of_nonneg_left hlogP hNnon
    have h2 := mul_le_mul_of_nonneg_right hNup (show 0 ≤ 4*Real.log t by linarith)
    nlinarith [hRS]
  refine ⟨hNp,hb,hcap,?_⟩
  change 2*((branching t : ℝ)+2)*P^(level t) ≤ _
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hP.ne'),
    Real.log_mul (by norm_num) (by positivity : ((branching t : ℝ)+2) ≠ 0),Real.log_pow]
  have h2 := log_two_bounds
  nlinarith

theorem eventual_choice : ∀ᶠ d : ℕ in atTop,
    1 ≤ level (Real.log (d : ℝ)) ∧ 2 ≤ branching (Real.log (d : ℝ)) ∧
      d ≤ branching (Real.log (d : ℝ))^level (Real.log (d : ℝ)) ∧
      2*((branching (Real.log (d : ℝ)) : ℝ)+2)*
        (1024*(1+(level (Real.log (d : ℝ)) : ℝ)*Real.log (branching (Real.log (d : ℝ)) : ℝ))^2)^level (Real.log (d : ℝ)) ≤
          Real.exp (32*Real.sqrt (Real.log (d : ℝ)*Real.log (Real.log (d : ℝ)))) := by
  have htend : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := htend.eventually (eventually_ge_atTop (1 : ℝ))
  have h2 := htend.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1024 : ℝ)))
  have h3 := htend.eventually (EditDepth.eventually_radius_large 0)
  filter_upwards [h1,h2,h3,eventually_ge_atTop (1 : ℕ)] with d ht hl hr hd
  have hr' : 2 ≤ EditDepth.radius (Real.log (d : ℝ)) := by norm_num at hr; linarith
  obtain ⟨hN,hb,hcap,hbound⟩ := choose_parameters ht hl hr'
  refine ⟨hN,hb,?_,hbound⟩
  rw [Real.exp_log (by exact_mod_cast (show 0 < d by omega))] at hcap
  exact_mod_cast hcap

end EditUpperParameters

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Alphabet-uniform upper bounds for least distortion
-/

namespace EditUpper
open EditDistortion EditCutModel
universe u

lemma model_E_bound (A : Type u) [Fintype A] [Nonempty A] {d : ℕ} (hd : 1 ≤ d)
    (M : Model (List A)) {D : ℝ} (hD : 0 ≤ D)
    (hlo : ∀ x y : List A, x.length ≤ d → y.length ≤ d → (indel x y : ℝ) ≤ M.dist x y)
    (hup : ∀ x y : List A, M.dist x y ≤ D*(indel x y : ℝ)) : E A d ≤ 2*D := by
  classical
  let : Finite (Words A d) := finite_words A d
  let x : Words A d := ⟨[],by simp⟩
  let y : Words A d := ⟨[Classical.arbitrary A],by simpa using hd⟩
  let : Nontrivial (Words A d) := ⟨⟨x,y,by simp [x,y]⟩⟩
  let f : Words A d ↪ L1 :=
    { toFun := fun z => M.vector z.val
      inj' := by
        intro v w he
        change M.vector v.val = M.vector w.val at he
        have hh := hlo v.val w.val v.property w.property
        rw [← M.vector_distance,he,sub_self,norm_zero] at hh
        have hz : indel v.val w.val = 0 := by exact_mod_cast le_antisymm hh (Nat.cast_nonneg _)
        exact Subtype.ext ((cost_eq_zero_iff (s := false)).mp hz) }
  apply (leastDistortion_le _ (fun z => edit_real_diag z.val)
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f).trans
  have hbound : distortion (fun v w : Words A d => (edit v.val w.val : ℝ)) f ≤ (2*D)*1 := by
    apply distortion_le_of_bounds _
      (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f (by positivity)
    · intro v w
      change ‖M.vector v.val-M.vector w.val‖ ≤ _
      rw [M.vector_distance]
      have hi : (indel v.val w.val : ℝ) ≤ 2*(edit v.val w.val : ℝ) := by
        exact_mod_cast indel_le_two_edit v.val w.val
      calc
        _ ≤ D*(indel v.val w.val : ℝ) := hup _ _
        _ ≤ D*(2*(edit v.val w.val : ℝ)) := mul_le_mul_of_nonneg_left hi hD
        _ = _ := by ring
    · intro v w
      change (edit v.val w.val : ℝ) ≤ 1*‖M.vector v.val-M.vector w.val‖
      rw [one_mul,M.vector_distance]
      exact (show (edit v.val w.val : ℝ) ≤ indel v.val w.val by
        exact_mod_cast edit_le_indel v.val w.val).trans (hlo _ _ v.property w.property)
  simpa using hbound

lemma level_E_bound (b N : ℕ) (hb : 1 ≤ b) (A : Type u) [Fintype A] [Nonempty A]
    {d : ℕ} (hd : 1 ≤ d) (hcap : d ≤ b^N) :
    E A d ≤ 2*(((b : ℝ)+2)*(growth b N)^N) := by
  obtain ⟨M,hlo,hup⟩ := exists_level b N hb N le_rfl A
  have hD : 0 ≤ ((b : ℝ)+2)*(growth b N)^N := by
    have hh := growth_ge (N := N) hb
    positivity
  exact model_E_bound A hd M hD
    (fun x y hx hy => hlo x y (hx.trans hcap) (hy.trans hcap)) hup

theorem eventual_upper : ∀ᶠ d : ℕ in Filter.atTop,
    (∀ (A : Type u) [Fintype A], 2 ≤ Fintype.card A → E A d ≤ exponentScale 32 d) ∧
    alphabetSup d ≤ exponentScale 32 d := by
  filter_upwards [EditUpperParameters.eventual_choice,Filter.eventually_ge_atTop (1 : ℕ)] with d hc hd
  rcases hc with ⟨hN,hb,hcap,hbound⟩
  let N := EditUpperParameters.level (Real.log (d : ℝ))
  let b := EditUpperParameters.branching (Real.log (d : ℝ))
  have hnum : 2*(((b : ℝ)+2)*(growth b N)^N) ≤ exponentScale 32 d := by
    simpa [growth,exponentScale,b,N,mul_assoc] using hbound
  constructor
  · intro A inst hA
    let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
    exact (level_E_bound b N (by omega) A hd hcap).trans hnum
  · apply csSup_le (s := {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d})
      ⟨E (Fin 2) d,2,by omega,rfl⟩
    rintro r ⟨n,hn,rfl⟩
    let : NeZero n := ⟨by omega⟩
    exact (level_E_bound b N (by omega) (Fin n) hd hcap).trans hnum

end EditUpper

end OAI
end

section
-- module Solutions.OAIQ12_ED.EditDistance_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-sided exponential bounds for edit-distance distortion
-/

universe u

theorem edit_distance_main_oai : EditDistortion.MainClaim.{u} := by
  obtain ⟨c,hc,dL,hL⟩ := EditLower.all_lower_clauses.{u}
  obtain ⟨dU,hU⟩ := Filter.eventually_atTop.mp EditUpper.eventual_upper.{u}
  refine ⟨c,32,hc,by norm_num,max dL dU,?_⟩
  intro d hd
  obtain ⟨hl,hw,hs⟩ := hL d ((le_max_left _ _).trans hd)
  obtain ⟨hu,hsu⟩ := hU d ((le_max_right _ _).trans hd)
  exact ⟨fun A inst hA => ⟨hl A hA,hu A hA⟩,hw,hs,hsu⟩

end OAI
end

theorem solution.{u} : type_of% @OAI.edit_distance_main_oai.{u} := @OAI.edit_distance_main_oai.{u}
