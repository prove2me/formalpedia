-- Prove2me | solution 1 for OnlineLearningOCO.Agnostic.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:14:25.779801+00:00
-- url     : https://prove2.me/submissions/e2953af2-6e1e-48bc-a463-1fdc62cf7eac

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_OnlineLearningOCO_Agnostic_expertAlg

set_option autoImplicit false

namespace E3D62

open UnderstandingML OnlineLearningOCO.Agnostic

/-! ### Littlestone dimension facts -/

section Ldim

variable {X : Type*}

lemma ldim_mono {W W' : Set (X → Bool)} (h : W ⊆ W') : ldim W ≤ ldim W' := by
  unfold ldim
  refine iSup₂_le fun d hd => ?_
  obtain ⟨v, hv⟩ := hd
  refine le_iSup₂_of_le (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree W' d v) =>
    (d : ℕ∞)) d ⟨v, fun y => ?_⟩ le_rfl
  obtain ⟨g, hg, hg'⟩ := hv y
  exact ⟨g, h hg, hg'⟩

lemma ldim_ge_of_tree {W : Set (X → Bool)} {d : ℕ} {v : List Bool → X}
    (hv : ShattersTree W d v) : (d : ℕ∞) ≤ ldim W := by
  unfold ldim
  exact le_iSup₂_of_le (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree W d v) =>
    (d : ℕ∞)) d ⟨v, hv⟩ le_rfl

lemma tree_trunc {W : Set (X → Bool)} {d k : ℕ} {v : List Bool → X}
    (hv : ShattersTree W d v) (hkd : k ≤ d) : ShattersTree W k v := by
  intro y
  classical
  let y' : Fin d → Bool := fun j => if hj : (j : ℕ) < k then y ⟨j, hj⟩ else false
  obtain ⟨g, hg, hgt⟩ := hv y'
  refine ⟨g, hg, fun t => ?_⟩
  have := hgt ⟨t, lt_of_lt_of_le t.2 hkd⟩
  have e1 : (fun j : Fin (t : ℕ) => y' ⟨j, lt_trans j.2 (lt_of_lt_of_le t.2 hkd)⟩) =
      (fun j : Fin (t : ℕ) => y ⟨j, lt_trans j.2 t.2⟩) := by
    funext j
    simp only [y', dif_pos (lt_trans j.2 t.2)]
  have e2 : y' ⟨t, lt_of_lt_of_le t.2 hkd⟩ = y t := by
    simp only [y', dif_pos t.2]
  simp only at this
  rw [e1, e2] at this
  exact this

lemma tree_of_ldim_ge {W : Set (X → Bool)} (x0 : X) (k : ℕ) (hk : (k : ℕ∞) ≤ ldim W)
    (hne : W.Nonempty) : ∃ v, ShattersTree W k v := by
  rcases k with _ | k
  · obtain ⟨g, hg⟩ := hne
    exact ⟨fun _ => x0, fun _ => ⟨g, hg, fun t => t.elim0⟩⟩
  · by_contra hno
    push Not at hno
    have : ldim W ≤ (k : ℕ∞) := by
      unfold ldim
      refine iSup₂_le fun d hd => ?_
      obtain ⟨v, hv⟩ := hd
      by_contra hlt
      push Not at hlt
      have hkd : k + 1 ≤ d := by exact_mod_cast hlt
      exact hno v (tree_trunc hv hkd)
    have h2 := hk.trans this
    have : k + 1 ≤ k := by exact_mod_cast h2
    omega

/-- The tree merge: root `y`, left subtree from `V^false`, right from `V^true`. -/
def mergeTree (y : X) (v0 v1 : List Bool → X) : List Bool → X
  | [] => y
  | b :: l => cond b (v1 l) (v0 l)

lemma ofFn_succ_val {k : ℕ} (yy : Fin (k + 1) → Bool) (s : Fin k) :
    List.ofFn (fun j : Fin ((Fin.succ s : Fin (k + 1)) : ℕ) =>
      yy ⟨j, lt_trans j.2 (Fin.succ s).2⟩) =
    yy 0 :: List.ofFn (fun j : Fin (s : ℕ) => yy (Fin.succ ⟨j, lt_trans j.2 s.2⟩)) := by
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    rcases m with _ | m
    · simp
    · simp

lemma merge_shatters {V : Set (X → Bool)} (y : X) {k : ℕ} {v0 v1 : List Bool → X}
    (h0 : ShattersTree (V ∩ {g | g y = false}) k v0)
    (h1 : ShattersTree (V ∩ {g | g y = true}) k v1) :
    ShattersTree V (k + 1) (mergeTree y v0 v1) := by
  intro yy
  have hsh : ShattersTree (V ∩ {g | g y = yy 0}) k (cond (yy 0) v1 v0) := by
    cases yy 0 <;> assumption
  obtain ⟨g, ⟨hgV, hgy⟩, hg⟩ := hsh (fun j => yy j.succ)
  refine ⟨g, hgV, fun t => ?_⟩
  refine Fin.cases ?_ (fun s => ?_) t
  · have hnil : List.ofFn (fun j : Fin ((0 : Fin (k + 1)) : ℕ) =>
        yy ⟨j, lt_trans j.2 (0 : Fin (k + 1)).2⟩) = [] := by
      rw [List.ofFn_eq_nil_iff]; simp
    rw [hnil]
    exact hgy
  · rw [ofFn_succ_val]
    have := hg s
    simp only [mergeTree]
    cases h : yy 0 <;> simp only [h, cond] at this ⊢ <;> exact this

lemma ldimBot_ne {W : Set (X → Bool)} (h : W.Nonempty) : ldimBot W = (ldim W : WithBot ℕ∞) := by
  classical
  unfold ldimBot; simp [h]

lemma ldimBot_empty {W : Set (X → Bool)} (h : ¬ W.Nonempty) : ldimBot W = ⊥ := by
  classical
  unfold ldimBot; simp [h]

/-- SOA key step: the minority side has strictly smaller Littlestone dimension. -/
lemma soa_drop (V : Set (X → Bool)) (y : X) (r : Bool)
    (hne : (V ∩ {g | g y = r}).Nonempty)
    (hle : ldimBot (V ∩ {g | g y = r}) ≤ ldimBot (V ∩ {g | g y = !r}))
    (hfin : ldim V ≠ ⊤) :
    ldim (V ∩ {g | g y = r}) + 1 ≤ ldim V := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  suffices hlt : ldim (V ∩ {g | g y = r}) < ldim V from Order.add_one_le_of_lt hlt
  by_contra hcon
  push Not at hcon
  rw [← hk] at hcon
  rw [ldimBot_ne hne] at hle
  have hne2 : (V ∩ {g | g y = !r}).Nonempty := by
    by_contra hn
    rw [ldimBot_empty hn] at hle
    exact absurd hle (by simp)
  rw [ldimBot_ne hne2, WithBot.coe_le_coe] at hle
  obtain ⟨v1, hv1⟩ := tree_of_ldim_ge y k hcon hne
  obtain ⟨v2, hv2⟩ := tree_of_ldim_ge y k (hcon.trans hle) hne2
  have hm : ShattersTree V (k + 1) (mergeTree y (cond r v2 v1) (cond r v1 v2)) := by
    cases r
    · exact merge_shatters y hv1 hv2
    · exact merge_shatters y hv2 hv1
  have := ldim_ge_of_tree hm
  rw [← hk] at this
  have : k + 1 ≤ k := by exact_mod_cast this
  omega

end Ldim

/-! ### The expert set recursion -/

section Experts

variable {X : Type*}

lemma expertSetAux_append (I : Finset ℕ) (y : X) (xs : List X) :
    ∀ (V : Set (X → Bool)) (t0 : ℕ), expertSetAux I V t0 (xs ++ [y]) =
      expertSetAux I V t0 xs ∩
        {g | g y = expertPred I (expertSetAux I V t0 xs) (t0 + xs.length) y} := by
  induction xs with
  | nil => intro V t0; simp [expertSetAux]
  | cons x xs ih =>
    intro V t0
    simp only [List.cons_append, expertSetAux, List.length_cons]
    rw [ih]
    rw [show t0 + 1 + xs.length = t0 + (xs.length + 1) by omega]

end Experts


/-! ### The run of a fixed hypothesis -/

section Run

variable {X : Type*} (H : Set (X → Bool)) (h : X → Bool) (xl : List X)

def Wt (t : ℕ) : Set (X → Bool) := {g ∈ H | ∀ y ∈ xl.take t, g y = h y}

def flipP (t : ℕ) : Prop := ∃ y, xl[t]? = some y ∧ h y ≠ expertTilde (Wt H h xl t) y

open Classical in
noncomputable def flipSet : Finset ℕ := (Finset.range xl.length).filter (flipP H h xl)

lemma Wt_succ (t : ℕ) (y : X) (hy : xl[t]? = some y) :
    Wt H h xl (t + 1) = Wt H h xl t ∩ {g | g y = h y} := by
  ext g
  simp only [Wt, List.take_succ, hy, Option.toList_some, Set.mem_setOf_eq, Set.mem_inter_iff,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hH, hall⟩
    exact ⟨⟨hH, fun z hz => hall z (Or.inl hz)⟩, hall y (Or.inr rfl)⟩
  · rintro ⟨⟨hH, hall⟩, hy'⟩
    refine ⟨hH, fun z hz => ?_⟩
    rcases hz with hz | rfl
    · exact hall z hz
    · exact hy'

lemma Wt_subset (t : ℕ) : Wt H h xl t ⊆ H := fun _ hg => hg.1

lemma mem_Wt (hh : h ∈ H) (t : ℕ) : h ∈ Wt H h xl t := ⟨hh, fun _ _ => rfl⟩

lemma expertPred_eq (I : Finset ℕ) (V : Set (X → Bool)) (t : ℕ) (y : X)
    (hiff : t ∈ I ↔ h y ≠ expertTilde V y) : expertPred I V t y = h y := by
  unfold expertPred
  by_cases ht : t ∈ I
  · rw [if_pos ht]
    have := hiff.mp ht
    cases h1 : h y <;> cases h2 : expertTilde V y <;> simp_all
  · rw [if_neg ht]
    have := mt hiff.mpr ht
    push Not at this
    exact this.symm

lemma expertSet_flip : ∀ t, t ≤ xl.length →
    expertSet H (flipSet H h xl) (xl.take t) = Wt H h xl t := by
  intro t
  induction t with
  | zero =>
    intro _
    ext g
    simp [expertSet, expertSetAux, Wt]
  | succ t ih =>
    intro ht
    have hlt : t < xl.length := by omega
    have hy : xl[t]? = some xl[t] := List.getElem?_eq_getElem hlt
    have htake : xl.take (t + 1) = xl.take t ++ [xl[t]] := by
      rw [List.take_succ, hy]; rfl
    rw [htake]
    unfold expertSet
    rw [expertSetAux_append]
    have ih' := ih (by omega)
    unfold expertSet at ih'
    rw [ih', List.length_take, min_eq_left hlt.le, Nat.zero_add, Wt_succ H h xl t _ hy]
    congr 1
    ext g
    simp only [Set.mem_setOf_eq]
    rw [expertPred_eq h]
    classical
    simp only [flipSet, Finset.mem_filter, Finset.mem_range, hlt, true_and, flipP, hy,
      Option.some.injEq]
    constructor
    · rintro ⟨z, rfl, hz⟩; exact hz
    · intro hz; exact ⟨_, rfl, hz⟩

open Classical in
lemma flip_count (hh : h ∈ H) (hfin : ldim H ≠ ⊤) : ∀ t, t ≤ xl.length →
    (((Finset.range t).filter (flipP H h xl)).card : ℕ∞) + ldim (Wt H h xl t) ≤ ldim H := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_add]
    exact ldim_mono (Wt_subset H h xl 0)
  | succ t ih =>
    intro ht
    have hlt : t < xl.length := by omega
    have hy : xl[t]? = some xl[t] := List.getElem?_eq_getElem hlt
    have ih' := ih (by omega)
    have hWfin : ldim (Wt H h xl t) ≠ ⊤ := by
      intro htop
      rw [htop] at ih'
      simp at ih'
      exact hfin ih'
    rw [Wt_succ H h xl t _ hy, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : flipP H h xl t
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      obtain ⟨z, hz, hflip⟩ := hp
      rw [hy, Option.some.injEq] at hz
      subst hz
      have hle : ldimBot (Wt H h xl t ∩ {g | g xl[t] = h xl[t]}) ≤
          ldimBot (Wt H h xl t ∩ {g | g xl[t] = !h xl[t]}) := by
        unfold expertTilde at hflip
        cases hr : h xl[t] <;> rw [hr] at hflip <;> simp at hflip ⊢
        · exact hflip.le
        · exact hflip
      have hdrop := soa_drop (Wt H h xl t) xl[t] (h xl[t])
        ⟨h, mem_Wt H h xl hh t, rfl⟩ hle hWfin
      calc ((((Finset.range t).filter (flipP H h xl)).card + 1 : ℕ) : ℕ∞) +
            ldim (Wt H h xl t ∩ {g | g xl[t] = h xl[t]})
          = (((Finset.range t).filter (flipP H h xl)).card : ℕ∞) +
            (ldim (Wt H h xl t ∩ {g | g xl[t] = h xl[t]}) + 1) := by
            push_cast; ring
        _ ≤ (((Finset.range t).filter (flipP H h xl)).card : ℕ∞) + ldim (Wt H h xl t) := by
            gcongr
        _ ≤ ldim H := ih'
    · rw [if_neg hp]
      calc (((Finset.range t).filter (flipP H h xl)).card : ℕ∞) +
            ldim (Wt H h xl t ∩ {g | g xl[t] = h xl[t]})
          ≤ (((Finset.range t).filter (flipP H h xl)).card : ℕ∞) + ldim (Wt H h xl t) := by
            gcongr
            exact ldim_mono Set.inter_subset_left
        _ ≤ ldim H := ih'

open Classical in
lemma flipSet_card (hh : h ∈ H) (L : ℕ) (hL : ldim H = L) : (flipSet H h xl).card ≤ L := by
  have := flip_count H h xl hh (by rw [hL]; exact ENat.natCast_ne_top L) xl.length le_rfl
  rw [hL] at this
  have h2 : (((Finset.range xl.length).filter (flipP H h xl)).card : ℕ∞) ≤ L :=
    le_trans le_self_add this
  have h3 : ((Finset.range xl.length).filter (flipP H h xl)).card ≤ L := by exact_mod_cast h2
  exact h3

lemma flipSet_sub : flipSet H h xl ⊆ Finset.range xl.length := by
  classical
  intro t ht
  unfold flipSet at ht
  exact (Finset.mem_filter.mp (by convert ht)).1

end Run

/-! ### Counting the experts -/

lemma card_expert_bound (T L : ℕ) (hL1 : 1 ≤ L) (hLT : L ≤ T) :
    (((Finset.range T).powerset.filter (fun I => I.card ≤ L)).card : ℝ) ≤
      (Real.exp 1 * T / L) ^ L := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hL : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set q : ℝ := (L : ℝ) / T with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hT]; exact_mod_cast hLT
  have h1 : (((Finset.range T).powerset.filter (fun I => I.card ≤ L)).card : ℝ) * q ^ L ≤
      (q + 1) ^ T := by
    calc (((Finset.range T).powerset.filter (fun I => I.card ≤ L)).card : ℝ) * q ^ L
        = ∑ I ∈ (Finset.range T).powerset.filter (fun I => I.card ≤ L), q ^ L := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ I ∈ (Finset.range T).powerset.filter (fun I => I.card ≤ L), q ^ I.card :=
          Finset.sum_le_sum fun I hI => pow_le_pow_of_le_one hq0 hq1 (Finset.mem_filter.mp hI).2
      _ ≤ ∑ I ∈ (Finset.range T).powerset, q ^ I.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => pow_nonneg hq0 _)
      _ = (q + 1) ^ T := by
          have := Finset.sum_pow_mul_eq_add_pow q 1 (Finset.range T)
          simpa using this
  have h2 : (q + 1) ^ T ≤ Real.exp L := by
    calc (q + 1) ^ T ≤ (Real.exp q) ^ T :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp q]) T
      _ = Real.exp (T * q) := (Real.exp_nat_mul q T).symm
      _ = Real.exp L := by congr 1; rw [hq]; field_simp
  have key : (Real.exp 1 * T / L) ^ L * q ^ L = Real.exp L := by
    rw [← mul_pow]
    have : Real.exp 1 * T / L * q = Real.exp 1 := by rw [hq]; field_simp
    rw [this, ← Real.exp_nat_mul, mul_one]
  have hqL : 0 < q ^ L := pow_pos (by positivity) L
  refine le_of_mul_le_mul_right ?_ hqL
  rw [key]
  exact h1.trans h2

/-! ### Hedge (copied from 6b387766, closed-form weights) -/

open MeasureTheory ProbabilityTheory in
lemma p6b_hoeff_fin {n : ℕ} (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n)) (ℓ : Fin n → ℝ)
    (hℓ : ∀ i, -1 ≤ ℓ i ∧ ℓ i ≤ 1) (s : ℝ) :
    ∑ i, w i * Real.exp (s * ℓ i) ≤ Real.exp (s * ∑ i, w i * ℓ i + s ^ 2 / 2) := by
  classical
  obtain ⟨hw0, hw1⟩ := hw
  let μ : Measure (Fin n) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac i
  have hμs : ∀ j, μ {j} = ENNReal.ofReal (w j) := by
    intro j
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator]
  have hμr : ∀ j, μ.real {j} = w j := by
    intro j
    rw [measureReal_def, hμs, ENNReal.toReal_ofReal (hw0 j)]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]
  have hint : ∀ f : Fin n → ℝ, ∫ x, f x ∂μ = ∑ i, w i * f i := by
    intro f
    rw [integral_fintype (Integrable.of_finite)]
    simp [hμr]
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := -1) (b := 1)
    (Measurable.of_discrete).aemeasurable (Filter.Eventually.of_forall fun i => ⟨(hℓ i).1, (hℓ i).2⟩)
  have h2 := hH.mgf_le s
  have hc : ((‖(1:ℝ) - -1‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : ‖(1:ℝ) - -1‖₊ = 2 := by
      ext; simp; norm_num
    rw [this]; norm_num
  rw [hc] at h2
  simp only [mgf, hint, NNReal.coe_one, one_mul] at h2
  set m := ∑ i, w i * ℓ i
  have key : ∑ i, w i * Real.exp (s * ℓ i) =
      Real.exp (s * m) * ∑ i, w i * Real.exp (s * (ℓ i - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, Real.exp_sub]; field_simp
  rw [key, Real.exp_add]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

lemma p6b_regret {n T : ℕ} (hn : 0 < n) (hT : 0 < T) (η : ℝ)
    (hη : η = Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ)))
    (ℓ : ℕ → Fin n → ℝ) (hℓ : ∀ t i, -1 ≤ ℓ t i ∧ ℓ t i ≤ 1) (x : ℕ → Fin n → ℝ)
    (hc : ∀ t i, x t i = Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j)) :
    (∀ t, x t ∈ stdSimplex ℝ (Fin n)) ∧
    ∀ i, ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j ≤
      ∑ t ∈ Finset.range T, ℓ t i + T * η := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set E : ℕ → Fin n → ℝ := fun t j => Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) with hEdef
  set Z : ℕ → ℝ := fun t => ∑ j, E t j with hZdef
  have hZpos : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hxs : ∀ t, x t ∈ stdSimplex ℝ (Fin n) := by
    intro t
    refine ⟨fun i => ?_, ?_⟩
    · rw [hc t i]; exact div_nonneg (Real.exp_pos _).le (hZpos t).le
    · simp_rw [hc t]; rw [← Finset.sum_div]; exact div_self (hZpos t).ne'
  refine ⟨hxs, ?_⟩
  intro i
  set m : ℕ → ℝ := fun t => ∑ j, x t j * ℓ t j with hm
  -- one-step potential bound
  have hstep : ∀ t, Z (t + 1) ≤ Z t * Real.exp (-η * m t + η ^ 2 / 2) := by
    intro t
    have hH := p6b_hoeff_fin (x t) (hxs t) (ℓ t) (hℓ t) (-η)
    rw [neg_sq] at hH
    have hEq : ∑ j, x t j * Real.exp (-η * ℓ t j) = Z (t + 1) / Z t := by
      simp_rw [hc t]
      rw [show Z (t + 1) = ∑ j, E t j * Real.exp (-η * ℓ t j) by
        simp only [hZdef, hEdef]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_range_succ, mul_add, Real.exp_add]]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hZdef, hEdef]; ring
    rw [hEq, div_le_iff₀ (hZpos t)] at hH
    calc Z (t + 1) ≤ Real.exp (-η * m t + η ^ 2 / 2) * Z t := by
          simpa [hm, mul_comm, mul_left_comm, mul_assoc] using hH
      _ = _ := by ring
  have hiter : ∀ N, Z N ≤ Z 0 * Real.exp (∑ t ∈ Finset.range N, (-η * m t + η ^ 2 / 2)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc Z (N + 1) ≤ Z N * Real.exp (-η * m N + η ^ 2 / 2) := hstep N
        _ ≤ Z 0 * Real.exp (∑ t ∈ Finset.range N, (-η * m t + η ^ 2 / 2)) *
              Real.exp (-η * m N + η ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add, Finset.sum_range_succ]
  have hZ0 : Z 0 = (n : ℝ) := by simp [hZdef, hEdef]
  have hlow : E T i ≤ Z T :=
    Finset.single_le_sum (f := E T) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog : -η * ∑ s ∈ Finset.range T, ℓ s i ≤
      Real.log n + ∑ t ∈ Finset.range T, (-η * m t + η ^ 2 / 2) := by
    have h := hlow.trans (hiter T)
    rw [hZ0, ← Real.exp_log hnpos, ← Real.exp_add] at h
    exact Real.exp_le_exp.mp h
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hη2 : η ^ 2 = 2 * Real.log n / T := by
    rw [hη, Real.sq_sqrt (by positivity)]
  have hlogeq : Real.log n = T * η ^ 2 / 2 := by
    rw [hη2]; field_simp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hlogeq] at hlog
  have hη0 : 0 ≤ η := by rw [hη]; exact Real.sqrt_nonneg _
  rcases hη0.lt_or_eq with hpos | hzero
  · -- η > 0
    have : η * (∑ t ∈ Finset.range T, m t) ≤ η * (∑ s ∈ Finset.range T, ℓ s i + T * η) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos
  · -- η = 0, so log n = 0, so n = 1
    have hl0 : Real.log (n : ℝ) = 0 := by rw [hlogeq, ← hzero]; ring
    have hn1 : n = 1 := by
      rcases Real.log_eq_zero.mp hl0 with h | h | h
      · exact absurd h hnpos.ne'
      · exact_mod_cast h
      · linarith
    subst hn1
    rw [← hzero, mul_zero, add_zero]
    refine Finset.sum_le_sum fun t _ => ?_
    have hsub : ∀ j : Fin 1, j = i := fun j => Subsingleton.elim _ _
    have h1 := (hxs t).2
    rw [Fin.sum_univ_one] at h1 ⊢
    rw [hsub 0] at h1 ⊢
    rw [h1, one_mul]



/-! ### The Hedge learner over the experts -/

section Learner

variable {X : Type*}

noncomputable def lossAt (H : Set (X → Bool)) {n : ℕ} (e : Fin n → Finset ℕ)
    (hist : List (X × Bool)) (i : Fin n) (s : ℕ) : ℝ :=
  match hist[s]? with
  | some p => |labelR (expertAlg H (e i) (hist.take s) p.1) - labelR p.2|
  | none => 0

noncomputable def hedgeAlg (H : Set (X → Bool)) {n : ℕ} (e : Fin n → Finset ℕ) (η : ℝ) :
    OnlineAlgR X := fun hist x =>
  ∑ i, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist i s) /
    (∑ j, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist j s)) *
    labelR (expertAlg H (e i) hist x)

lemma labelR_bounds (b : Bool) : 0 ≤ labelR b ∧ labelR b ≤ 1 := by
  cases b <;> simp [labelR]

lemma abs_labelR_bounds (a b : Bool) : 0 ≤ |labelR a - labelR b| ∧ |labelR a - labelR b| ≤ 1 := by
  cases a <;> cases b <;> simp [labelR]

lemma lossAt_bounds (H : Set (X → Bool)) {n : ℕ} (e : Fin n → Finset ℕ)
    (hist : List (X × Bool)) (i : Fin n) (s : ℕ) :
    0 ≤ lossAt H e hist i s ∧ lossAt H e hist i s ≤ 1 := by
  unfold lossAt
  split
  · exact abs_labelR_bounds _ _
  · simp

lemma lossAt_take (H : Set (X → Bool)) {n : ℕ} (e : Fin n → Finset ℕ)
    (l : List (X × Bool)) (i : Fin n) {s t : ℕ} (hst : s < t) :
    lossAt H e (l.take t) i s = lossAt H e l i s := by
  unfold lossAt
  rw [List.getElem?_take, if_pos hst, List.take_take, min_eq_left hst.le]

lemma hedge_weights_simplex (H : Set (X → Bool)) {n : ℕ} (hn : 0 < n) (e : Fin n → Finset ℕ)
    (η : ℝ) (hist : List (X × Bool)) :
    (fun i => Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist i s) /
      (∑ j, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist j s))) ∈
      stdSimplex ℝ (Fin n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hZ : 0 < ∑ j, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist j s) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨fun i => div_nonneg (Real.exp_pos _).le hZ.le, ?_⟩
  rw [← Finset.sum_div]; exact div_self hZ.ne'

lemma hedgeAlg_mem (H : Set (X → Bool)) {n : ℕ} (hn : 0 < n) (e : Fin n → Finset ℕ)
    (η : ℝ) (hist : List (X × Bool)) (x : X) : hedgeAlg H e η hist x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hw0, hw1⟩ := hedge_weights_simplex H hn e η hist
  unfold hedgeAlg
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (labelR_bounds _).1
  · calc _ ≤ ∑ i, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist i s) /
            (∑ j, Real.exp (-η * ∑ s ∈ Finset.range hist.length, lossAt H e hist j s)) * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (labelR_bounds _).2 (hw0 i)
      _ = 1 := by simp only [mul_one]; exact hw1

lemma mix_abs_le {n : ℕ} (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n)) (a : Fin n → ℝ)
    (b : ℝ) : |∑ i, w i * a i - b| ≤ ∑ i, w i * |a i - b| := by
  obtain ⟨hw0, hw1⟩ := hw
  have : ∑ i, w i * a i - b = ∑ i, w i * (a i - b) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_of_nonneg (hw0 i)]

end Learner

end E3D62

open UnderstandingML OnlineLearningOCO.Agnostic in
theorem solution {X : Type*} (H : Set (X → Bool)) (L : ℕ) (hL : ldim H = L) (T : ℕ)
    (hLT : L ≤ T) :
    ∃ A : OnlineAlgR X, (∀ hist x, A hist x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (S : Fin T → X × Bool), ∀ h ∈ H,
        cumLoss A S - cumLossHyp h S ≤
          2 * Real.sqrt (L * Real.log (Real.exp 1 * T / L) * T) := by
  classical
  set E : Finset (Finset ℕ) := (Finset.range T).powerset.filter (fun I => I.card ≤ L) with hE
  set n := E.card with hndef
  have hn : 0 < n := Finset.card_pos.mpr ⟨∅, by simp [hE]⟩
  let e : Fin n → Finset ℕ := fun i => (E.equivFin.symm i).1
  set η := Real.sqrt (2 * Real.log n / T) with hη
  refine ⟨E3D62.hedgeAlg H e η, fun hist x => E3D62.hedgeAlg_mem H hn e η hist x, ?_⟩
  intro S h hh
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0
    simp only [cumLoss, cumLossHyp, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    positivity
  -- the run of `h`
  set xl : List X := (List.ofFn S).map Prod.fst with hxl
  have hxllen : xl.length = T := by simp [hxl]
  set I := E3D62.flipSet H h xl with hIdef
  have hIE : I ∈ E := by
    rw [hE, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, E3D62.flipSet_card H h xl hh L hL⟩
    have := E3D62.flipSet_sub H h xl
    rw [hxllen] at this
    exact this
  set istar : Fin n := E.equivFin ⟨I, hIE⟩ with histar
  have he : e istar = I := by simp [e, histar]
  have hexp : ∀ t : Fin T, expertAlg H I (history S t) (S t).1 = h (S t).1 := by
    intro t
    have hmap : (history S t).map Prod.fst = xl.take t := by
      simp [history, hxl, List.map_take]
    have hlen : (history S t).length = t := by simp [history]
    unfold expertAlg
    rw [hmap, hlen, E3D62.expertSet_flip H h xl t (by omega)]
    apply E3D62.expertPred_eq
    have hy : xl[(t : ℕ)]? = some (S t).1 := by simp [hxl]
    have htl : (t : ℕ) < xl.length := by omega
    simp only [hIdef, E3D62.flipSet, Finset.mem_filter, Finset.mem_range, htl, true_and, E3D62.flipP, hy,
      Option.some.injEq]
    constructor
    · rintro ⟨z, rfl, hz⟩; exact hz
    · intro hz; exact ⟨_, rfl, hz⟩
  -- losses and weights
  set ℓ : ℕ → Fin n → ℝ := fun s i => E3D62.lossAt H e (List.ofFn S) i s with hℓ
  have hℓt : ∀ t : Fin T, ∀ i, ℓ t i =
      |labelR (expertAlg H (e i) (history S t) (S t).1) - labelR (S t).2| := by
    intro t i
    simp [hℓ, E3D62.lossAt, history]
  set x : ℕ → Fin n → ℝ := fun t i => Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) with hx
  have hwt : ∀ t : Fin T, E3D62.hedgeAlg H e η (history S t) (S t).1 =
      ∑ i, x t i * labelR (expertAlg H (e i) (history S t) (S t).1) := by
    intro t
    have hlen : (history S t).length = t := by simp [history]
    have hsum : ∀ i, ∑ s ∈ Finset.range (history S t).length, E3D62.lossAt H e (history S t) i s =
        ∑ s ∈ Finset.range t, ℓ s i := by
      intro i
      rw [hlen]
      refine Finset.sum_congr rfl fun s hs => ?_
      exact E3D62.lossAt_take H e (List.ofFn S) i (Finset.mem_range.mp hs)
    unfold E3D62.hedgeAlg
    simp only [hsum, hx]
  obtain ⟨hsimp, hreg⟩ := E3D62.p6b_regret hn hT η rfl ℓ
    (fun t i => ⟨by linarith [(E3D62.lossAt_bounds H e (List.ofFn S) i t).1],
      (E3D62.lossAt_bounds H e (List.ofFn S) i t).2⟩) x (fun t i => rfl)
  have hround : ∀ t : Fin T, |E3D62.hedgeAlg H e η (history S t) (S t).1 - labelR (S t).2| ≤
      ∑ i, x t i * ℓ t i := by
    intro t
    rw [hwt t]
    refine (E3D62.mix_abs_le (x t) (hsimp t) _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hℓt t i]
  have hcum : cumLoss (E3D62.hedgeAlg H e η) S ≤ ∑ t ∈ Finset.range T, ∑ i, x t i * ℓ t i := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ i, x t i * ℓ t i) T]
    exact Finset.sum_le_sum fun t _ => hround t
  have hhyp : ∑ t ∈ Finset.range T, ℓ t istar = cumLossHyp h S := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => ℓ t istar) T]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hℓt t istar, he, hexp t]
  have hregret : cumLoss (E3D62.hedgeAlg H e η) S - cumLossHyp h S ≤ T * η := by
    have := hreg istar
    rw [hhyp] at this
    linarith
  -- the expert count
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : Real.log n ≤ L * Real.log (Real.exp 1 * T / L) := by
    rcases Nat.eq_zero_or_pos L with hL0 | hL1
    · have hE1 : E = {∅} := by
        ext J
        simp only [hE, hL0, Finset.mem_filter, Finset.mem_powerset, Nat.le_zero,
          Finset.card_eq_zero, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
      have : n = 1 := by rw [hndef, hE1]; rfl
      rw [this, hL0]; simp
    · have hb := E3D62.card_expert_bound T L hL1 hLT
      rw [← hE, ← hndef] at hb
      calc Real.log n ≤ Real.log ((Real.exp 1 * T / L) ^ L) := Real.log_le_log hnr hb
        _ = L * Real.log (Real.exp 1 * T / L) := by rw [Real.log_pow]
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hTη : (T : ℝ) * η = Real.sqrt (2 * Real.log n * T) := by
    have : 2 * Real.log n * (T : ℝ) = (T : ℝ) ^ 2 * (2 * Real.log n / T) := by
      field_simp
    rw [hη, this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hTr.le]
  have h2 : 2 * Real.sqrt (L * Real.log (Real.exp 1 * T / L) * T) =
      Real.sqrt (4 * (L * Real.log (Real.exp 1 * T / L) * T)) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) (L * Real.log (Real.exp 1 * T / L) * T), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  refine hregret.trans ?_
  rw [hTη, h2]
  apply Real.sqrt_le_sqrt
  nlinarith
