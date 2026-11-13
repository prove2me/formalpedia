-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:27:03.972637+00:00
-- url     : https://prove2.me/submissions/bd83730c-e53d-4178-bc9e-eece68f6ac1b

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

section
set_option autoImplicit false

/-!
# Basic facts about normalized product functions (shared by Lemmas 3.2–3.4)

* F1: `component` of a normalized product function is its factor; norm one, nonzero.
* F2: `proj σs K P` is a normalized product function with components
  `if i ∈ K then component σs P i else 1`.
* F3: powers: `P ^ N = 1 → (proj σs K P) ^ N = 1`; `orderOf (proj σs K P) ∣ orderOf P`.
* F4: rigidity of product decompositions over a nonempty alphabet, and the extraction of a
  small exceptional set from `symbolicDist F 1 < D`.
-/

namespace RestrictedAP.Counting.Dev.ProdBasics
open RestrictedAP.Counting

/-! ## F4: rigidity -/

/-- Evaluating a product decomposition at `s` updated in coordinate `i`. -/
theorem prod_update_eq {α : Type*} {n : ℕ} (w : Fin n → α → ℂ) (s : Fin n → α) (i : Fin n)
    (a : α) :
    ∏ j, w j (Function.update s i a j) = w i a * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    simp [Function.update_of_ne this]

theorem prod_compl_ne_zero {α : Type*} {n : ℕ} (w : Fin n → α → ℂ) (hw : ∀ i a, w i a ≠ 0)
    (s : Fin n → α) (i : Fin n) : ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => hw j (s j)

/-- Ratio identity: two decompositions of the same function, `w` nonzero; if the `i`-th factor
of `w'` is constant then so is the `i`-th factor of `w`. -/
theorem rigid_eq {α : Type*} [Nonempty α] {n : ℕ} (w w' : Fin n → α → ℂ)
    (hw : ∀ i a, w i a ≠ 0) (h : ∀ t : Fin n → α, ∏ i, w i (t i) = ∏ i, w' i (t i))
    (i : Fin n) (hc : ∀ a b, w' i a = w' i b) (a b : α) : w i a = w i b := by
  classical
  obtain ⟨s0⟩ := (inferInstance : Nonempty α)
  let s : Fin n → α := fun _ => s0
  have ha := h (Function.update s i a)
  have hb := h (Function.update s i b)
  rw [prod_update_eq, prod_update_eq] at ha hb
  have hR := prod_compl_ne_zero w hw s i
  have : w i a * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) =
      w i b * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) := by
    rw [ha, hb, hc a b]
  exact mul_right_cancel₀ hR this

/-- F4(a): if `∏ w i (t i)` is constant (with `w` nonzero) then every factor is constant. -/
theorem rigid_const {α : Type*} [Nonempty α] {n : ℕ} (w : Fin n → α → ℂ)
    (hw : ∀ i a, w i a ≠ 0) (c : ℂ) (h : ∀ t : Fin n → α, ∏ i, w i (t i) = c)
    (i : Fin n) (a b : α) : w i a = w i b := by
  classical
  obtain ⟨s0⟩ := (inferInstance : Nonempty α)
  let s : Fin n → α := fun _ => s0
  have ha := h (Function.update s i a)
  have hb := h (Function.update s i b)
  rw [prod_update_eq] at ha hb
  exact mul_right_cancel₀ (prod_compl_ne_zero w hw s i) (ha.trans hb.symm)

open Classical in
/-- The defining set of `symbolicDist F 1` is nonempty when `F` has a norm-one decomposition. -/
theorem symbolicDist_set_nonempty {α : Type*} {n : ℕ} (F : (Fin n → α) → ℂ)
    (w : Fin n → α → ℂ) (hw : ∀ i a, ‖w i a‖ = 1) (hF : ∀ t, F t = ∏ i, w i (t i)) :
    {k | ∃ u v : Fin n → α → ℂ, (∀ i a, ‖u i a‖ = 1) ∧ (∀ i a, ‖v i a‖ = 1) ∧
      (∀ x, F x = ∏ i, u i (x i)) ∧ (∀ x, (1 : (Fin n → α) → ℂ) x = ∏ i, v i (x i)) ∧
      (Finset.univ.filter (fun i => u i ≠ v i)).card = k}.Nonempty :=
  ⟨_, w, fun _ _ => 1, hw, fun _ _ => norm_one, hF, fun _ => by simp, rfl⟩

open Classical in
/-- F4(b): if `F = ∏ w` with norm-one factors and `symbolicDist F 1 < D`, then outside a set
`J'` of size `< D` every factor `w i` is constant. -/
theorem symbolicDist_lt_const {α : Type*} [Nonempty α] {n : ℕ} (F : (Fin n → α) → ℂ)
    (w : Fin n → α → ℂ) (hw : ∀ i a, ‖w i a‖ = 1) (hF : ∀ t, F t = ∏ i, w i (t i)) (D : ℝ)
    (hD : (symbolicDist F 1 : ℝ) < D) :
    ∃ J' : Finset (Fin n), (J'.card : ℝ) < D ∧ ∀ i, i ∉ J' → ∀ a b, w i a = w i b := by
  classical
  have hmem := Nat.sInf_mem (symbolicDist_set_nonempty F w hw hF)
  obtain ⟨u, v, hu, hv, hFu, h1v, hcard⟩ := hmem
  have hv0 : ∀ i a, v i a ≠ 0 := fun i a h => by simpa [h] using hv i a
  have hw0 : ∀ i a, w i a ≠ 0 := fun i a h => by simpa [h] using hw i a
  refine ⟨Finset.univ.filter (fun i => u i ≠ v i), ?_, ?_⟩
  · have : ((Finset.univ.filter (fun i => u i ≠ v i)).card : ℝ) = (symbolicDist F 1 : ℝ) := by
      unfold symbolicDist
      convert congrArg (fun k : ℕ => (k : ℝ)) hcard
    rw [this]; exact hD
  · intro i hi a b
    have hiuv : u i = v i := by simpa using hi
    have hvc : ∀ a b, v i a = v i b :=
      rigid_const v hv0 1 (fun t => by have := h1v t; simpa using this.symm) i
    refine rigid_eq w u hw0 (fun t => by rw [← hF, hFu]) i ?_ a b
    intro a b; rw [hiuv]; exact hvc a b

/-! ## F1: components -/

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

theorem component_eq_factor (σs : Sig) (P : (Fin n → Sig) → ℂ) (u : Fin n → Sig → ℂ)
    (hu1 : ∀ i, u i σs = 1) (hP : ∀ x, P x = ∏ i, u i (x i)) (i : Fin n) (a : Sig) :
    component σs P i a = u i a := by
  unfold component
  rw [hP, prod_update_eq]
  simp [hu1]

theorem component_norm (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (i : Fin n) (a : Sig) : ‖component σs P i a‖ = 1 := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [component_eq_factor σs P u hu1 hPu]; exact hu i a

/-! ## F2: projections -/

/-! ## F3: powers and orders -/

theorem pow_apply_eq_one {α : Type*} (P : α → ℂ) (N : ℕ) (h : P ^ N = 1) (x : α) :
    P x ^ N = 1 := by
  have := congrFun h x; simpa using this

theorem component_pow (σs : Sig) (P : (Fin n → Sig) → ℂ) (N : ℕ) (h : P ^ N = 1) (i : Fin n)
    (a : Sig) : component σs P i a ^ N = 1 :=
  pow_apply_eq_one P N h _

theorem proj_pow_apply (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) (N : ℕ)
    (h : P ^ N = 1) (x : Fin n → Sig) : proj σs K P x ^ N = 1 := by
  unfold proj
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => component_pow σs P N h i (x i)

theorem proj_pow_orderOf_apply (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ)
    (x : Fin n → Sig) : proj σs K P x ^ orderOf P = 1 :=
  proj_pow_apply σs K P _ (pow_orderOf_eq_one P) x

/-- `z ^ m` for `z ^ N = 1`, `N > 0`, depends only on `m mod N`. -/
theorem zpow_eq_pow_emod (z : ℂ) (N : ℕ) (hN : 0 < N) (hz : z ^ N = 1) (m : ℤ) :
    z ^ m = z ^ (m % (N : ℤ)).toNat := by
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hz; exact zero_ne_one hz
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hr : (0 : ℤ) ≤ m % (N : ℤ) := Int.emod_nonneg _ hNz.ne'
  conv_lhs => rw [← Int.emod_add_mul_ediv m N]
  rw [zpow_add₀ hz0, zpow_mul, zpow_natCast, hz, one_zpow, mul_one,
    ← zpow_natCast, Int.toNat_of_nonneg hr]

end RestrictedAP.Counting.Dev.ProdBasics
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.L33
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics
open Classical

variable {Sig : Type} [Fintype Sig] [DecidableEq Sig] {n : ℕ}

/-- The lift along coordinate `s` of `Sig³`: `lift1/2/3` for `s = 0, 1, 2`. -/
def Lg (μ : Sig × Sig × Sig → ℝ) (s : Fin 3) (P : (Fin n → Sig) → ℂ) :
    (Fin n → {t // μ t ≠ 0}) → ℂ :=
  fun t => P (fun i => coord3 s (t i).1)

theorem lift1_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift1 μ P = Lg μ 0 P := by
  funext t; simp [lift1, Lg, coord3]

theorem lift2_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift2 μ P = Lg μ 1 P := by
  funext t; simp [lift2, Lg, coord3]

theorem lift3_eq (μ : Sig × Sig × Sig → ℝ) (P : (Fin n → Sig) → ℂ) : lift3 μ P = Lg μ 2 P := by
  funext t; simp [lift3, Lg, coord3]

/-- The joint lift of a projected collection, as an image of `PP × Fin 3`. -/
theorem jointLift_eq (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (K : Finset (Fin n))
    (PP : Finset ((Fin n → Sig) → ℂ)) :
    jointLift μ (projColl σs K PP) (projColl σs K PP) (projColl σs K PP) =
      (Finset.univ : Finset (PP × Fin 3)).image (fun x => Lg μ x.2 (proj σs K x.1.1)) := by
  ext f
  simp only [jointLift, projColl, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, Subtype.exists]
  constructor
  · rintro ((⟨Q, ⟨P, hP, rfl⟩, rfl⟩ | ⟨Q, ⟨P, hP, rfl⟩, rfl⟩) | ⟨Q, ⟨P, hP, rfl⟩, rfl⟩)
    · exact ⟨P, hP, 0, (lift1_eq μ _).symm⟩
    · exact ⟨P, hP, 1, (lift2_eq μ _).symm⟩
    · exact ⟨P, hP, 2, (lift3_eq μ _).symm⟩
  · rintro ⟨P, hP, s, rfl⟩
    fin_cases s
    · exact Or.inl (Or.inl ⟨_, ⟨P, hP, rfl⟩, lift1_eq μ _⟩)
    · exact Or.inl (Or.inr ⟨_, ⟨P, hP, rfl⟩, lift2_eq μ _⟩)
    · exact Or.inr ⟨_, ⟨P, hP, rfl⟩, lift3_eq μ _⟩

/-- Re-indexing an integer-exponent product over an image. -/
theorem prod_image_zpow {ι γ : Type*} [DecidableEq ι] [DecidableEq (γ → ℂ)] (g : ι → γ → ℂ)
    (a : (γ → ℂ) → ℤ) (X : Finset ι) :
    ∃ b : ι → ℤ, ∀ t, ∏ f ∈ X.image g, (f t) ^ (a f) = ∏ x ∈ X, (g x t) ^ (b x) := by
  induction X using Finset.induction_on with
  | empty => exact ⟨0, fun t => by simp⟩
  | insert x X hx ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hg : g x ∈ X.image g
    · refine ⟨Function.update b x 0, fun t => ?_⟩
      rw [Finset.image_insert, Finset.insert_eq_of_mem hg, hb, Finset.prod_insert hx]
      simp only [Function.update_self, zpow_zero, one_mul]
      refine Finset.prod_congr rfl fun y hy => ?_
      have : y ≠ x := fun h => hx (h ▸ hy)
      rw [Function.update_of_ne this]
    · refine ⟨Function.update b x (a (g x)), fun t => ?_⟩
      rw [Finset.image_insert, Finset.prod_insert hg, hb, Finset.prod_insert hx]
      simp only [Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun y hy => ?_
      have : y ≠ x := fun h => hx (h ▸ hy)
      rw [Function.update_of_ne this]

/-- The natural `i`-th factor of `F_K(e)`. -/
noncomputable def W (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ)) (e : PP × Fin 3 → ℕ)
    (i : Fin n) (a : Sig × Sig × Sig) : ℂ :=
  ∏ x : PP × Fin 3, (component σs x.1.1 i (coord3 x.2 a)) ^ (e x)

theorem prod_Lg_proj (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (K : Finset (Fin n)) (e : PP × Fin 3 → ℕ) (t : Fin n → {t // μ t ≠ 0}) :
    ∏ x : PP × Fin 3, (Lg μ x.2 (proj σs K x.1.1) t) ^ (e x) = ∏ i ∈ K, W σs PP e i (t i).1 := by
  simp only [Lg, proj, W, ← Finset.prod_pow]
  exact Finset.prod_comm

theorem W_norm (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P) (e : PP × Fin 3 → ℕ) (i : Fin n)
    (a : Sig × Sig × Sig) : ‖W σs PP e i a‖ = 1 := by
  unfold W
  rw [norm_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [norm_pow, component_norm σs _ (hPP _ x.1.2), one_pow]

/-- `e` has a constant `i`-th factor on the support of `μ`. -/
def good (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (e : PP × Fin 3 → ℕ) (i : Fin n) : Prop :=
  ∀ a b : {t // μ t ≠ 0}, W σs PP e i a.1 = W σs PP e i b.1

/-- Reduced exponent vectors. -/
noncomputable def E (PP : Finset ((Fin n → Sig) → ℂ)) : Finset (PP × Fin 3 → ℕ) :=
  Fintype.piFinset (fun x : PP × Fin 3 => Finset.range (orderOf x.1.1))

/-- The relations surviving on the kept coordinates `K`. -/
noncomputable def R (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    (K : Finset (Fin n)) : Finset (PP × Fin 3 → ℕ) :=
  (E PP).filter (fun e => ∀ i ∈ K, good μ σs PP e i)

theorem card_E (M : ℕ) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, orderOf P ≤ M) : (E PP).card ≤ M ^ (3 * PP.card) := by
  unfold E
  rw [Fintype.card_piFinset]
  simp only [Finset.card_range]
  calc ∏ x : PP × Fin 3, orderOf x.1.1 ≤ M ^ (Finset.univ : Finset (PP × Fin 3)).card :=
        Finset.prod_le_pow_card _ _ _ fun x _ => hPP _ x.1.2
    _ = M ^ (3 * PP.card) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, mul_comm]

/-- One step: failure of softrank on `K` yields a new relation surviving on `K \ J'`. -/
theorem step (μ : Sig × Sig × Sig → ℝ) (hA : Nonempty {t // μ t ≠ 0}) (σs : Sig)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P) (K : Finset (Fin n)) (d : ℤ)
    (h : ¬ SoftRankMuAtLeast μ (projColl σs K PP) (d : ℝ)) :
    ∃ J' : Finset (Fin n), (J'.card : ℤ) < d ∧
      ∃ e ∈ E PP, ¬ (∀ i ∈ K, good μ σs PP e i) ∧ ∀ i ∈ K \ J', good μ σs PP e i := by
  unfold SoftRankMuAtLeast SoftRankAtLeast at h
  push_neg at h
  obtain ⟨a, hnc, hlt⟩ := h
  rw [jointLift_eq] at hnc hlt
  obtain ⟨b, hb⟩ := prod_image_zpow (fun x : PP × Fin 3 => Lg μ x.2 (proj σs K x.1.1)) a
    Finset.univ
  let e : PP × Fin 3 → ℕ := fun x => (b x % (orderOf x.1.1 : ℤ)).toNat
  have hS : ∀ t, ∏ f ∈ (Finset.univ : Finset (PP × Fin 3)).image
      (fun x => Lg μ x.2 (proj σs K x.1.1)), (f t) ^ (a f) = ∏ i ∈ K, W σs PP e i (t i).1 := by
    intro t
    rw [hb, ← prod_Lg_proj]
    refine Finset.prod_congr rfl fun x _ => ?_
    exact zpow_eq_pow_emod _ _ (hPP _ x.1.2).2
      (proj_pow_orderOf_apply σs K x.1.1 _) (b x)
  have heE : e ∈ E PP := by
    simp only [E, Fintype.mem_piFinset, Finset.mem_range]
    intro x
    have h1 := Int.emod_nonneg (b x) (show ((orderOf x.1.1 : ℕ) : ℤ) ≠ 0 by
      have := (hPP _ x.1.2).2; omega)
    have h2 := Int.emod_lt_of_pos (b x) (show (0 : ℤ) < (orderOf x.1.1 : ℕ) by
      have := (hPP _ x.1.2).2; omega)
    show (b x % (orderOf x.1.1 : ℤ)).toNat < orderOf x.1.1
    omega
  let w' : Fin n → {t // μ t ≠ 0} → ℂ := fun i a => if i ∈ K then W σs PP e i a.1 else 1
  have hw' : ∀ i a, ‖w' i a‖ = 1 := by
    intro i a; simp only [w']; split_ifs
    · exact W_norm σs PP (fun P hP => (hPP P hP).1) e i a.1
    · exact norm_one
  have hSw : ∀ t, (fun x => ∏ f ∈ (Finset.univ : Finset (PP × Fin 3)).image
      (fun x => Lg μ x.2 (proj σs K x.1.1)), (f x) ^ (a f)) t = ∏ i, w' i (t i) := by
    intro t
    simp only [w']
    rw [hS, Finset.prod_ite_mem, Finset.univ_inter]
  obtain ⟨J', hJ', hconst⟩ := symbolicDist_lt_const _ w' hw' hSw (d : ℝ) hlt
  refine ⟨J', by exact_mod_cast hJ', e, heE, ?_, ?_⟩
  · intro hall
    obtain ⟨a0⟩ := hA
    obtain ⟨t, ht⟩ := hnc (∏ i ∈ K, W σs PP e i a0.1)
    apply ht
    rw [hS]
    exact Finset.prod_congr rfl fun i hi => hall i hi (t i) a0
  · intro i hi a b
    rw [Finset.mem_sdiff] at hi
    have := hconst i hi.2 a b
    simpa [w', hi.1] using this

theorem R_mono (μ : Sig × Sig × Sig → ℝ) (σs : Sig) (PP : Finset ((Fin n → Sig) → ℂ))
    {K K' : Finset (Fin n)} (h : K' ⊆ K) : R μ σs PP K ⊆ R μ σs PP K' := by
  intro e he
  simp only [R, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun i hi => he.2 i (h hi)⟩

theorem iter (μ : Sig × Sig × Sig → ℝ) (hA : Nonempty {t // μ t ≠ 0}) (σs : Sig) (M : ℕ)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M) (D : ℕ → ℤ) :
    ∀ m : ℕ, ∀ (i : ℕ) (K : Finset (Fin n)), 1 ≤ i → (E PP).card + 1 - i ≤ m →
      (Kᶜ.card : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j → i ≤ (R μ σs PP K).card →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ M ^ (3 * PP.card) ∧
        ∃ J : Finset (Fin n), (J.card : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j ∧
          SoftRankMuAtLeast μ (projColl σs Jᶜ PP) (D i : ℝ) := by
  have hRE : ∀ K, (R μ σs PP K).card ≤ (E PP).card := fun K => Finset.card_filter_le _ _
  have hEM := card_E M PP fun P hP => (hPP P hP).2.2
  intro m
  induction m with
  | zero =>
    intro i K hi hm _ hR
    have := hRE K
    omega
  | succ m ih =>
    intro i K hi hm hK hR
    by_cases hs : SoftRankMuAtLeast μ (projColl σs K PP) (D i : ℝ)
    · refine ⟨i, hi, le_trans hR (le_trans (hRE K) hEM), Kᶜ, hK, ?_⟩
      rwa [compl_compl]
    · obtain ⟨J', hJ', e, heE, hnot, hgood⟩ :=
        step μ hA σs PP (fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.1⟩) K (D i) hs
      have hsub : R μ σs PP K ⊂ R μ σs PP (K \ J') := by
        rw [Finset.ssubset_iff_of_subset (R_mono μ σs PP Finset.sdiff_subset)]
        refine ⟨e, ?_, ?_⟩
        · simp only [R, Finset.mem_filter]; exact ⟨heE, hgood⟩
        · simp only [R, Finset.mem_filter]; exact fun h => hnot h.2
      have hcard := Finset.card_lt_card hsub
      have hRK := hRE K
      refine ih (i + 1) (K \ J') (by omega) (by omega) ?_ (by omega)
      rw [Finset.sum_Ico_succ_top hi]
      have hc : (K \ J')ᶜ ⊆ Kᶜ ∪ J' := by
        intro x; simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]; tauto
      have h1 := Finset.card_le_card hc
      have h2 := Finset.card_union_le Kᶜ J'
      have h3 : ((K \ J')ᶜ.card : ℤ) ≤ (Kᶜ.card : ℤ) + J'.card := by exact_mod_cast h1.trans h2
      linarith

end RestrictedAP.Counting.Dev.L33

namespace RestrictedAP.Counting

open RestrictedAP.Counting.Dev.L33 in
theorem chk_lemma_3_3 (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig)
    (μ : Sig × Sig × Sig → ℝ) (hμ : IsDist μ) (n M : ℕ)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P)
    (D : ℕ → ℤ) (hD : ∀ j, 1 ≤ j → j < M ^ (3 * PP.card) → D j ≤ D (j + 1)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ M ^ (3 * PP.card) ∧
      ∃ J : Finset (Fin n), (J.card : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j ∧
        SoftRankMuAtLeast μ (projColl σs Jᶜ PP) (D i : ℝ) := by
  have hA : Nonempty {t // μ t ≠ 0} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : ∀ t, μ t = 0 := fun t => by_contra fun h => hne.false ⟨t, h⟩
    have := hμ.2
    simp [h0] at this
  have hPP' : ∀ P ∈ PP, IsProductFunction σs P ∧ 0 < orderOf P ∧ orderOf P ≤ M :=
    fun P hP => ⟨(hPP P hP).1, (hPP P hP).2.2.1, (hPP P hP).2.2.2⟩
  have h0 : (0 : PP × Fin 3 → ℕ) ∈ R μ σs PP Finset.univ := by
    simp only [R, E, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun x => (hPP' _ x.1.2).2.1, fun i _ a b => ?_⟩
    simp [W]
  exact iter μ hA σs M PP hPP' D _ 1 Finset.univ le_rfl le_rfl (by simp)
    (Finset.card_pos.mpr ⟨_, h0⟩)

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_3_3 := @RestrictedAP.Counting.chk_lemma_3_3
