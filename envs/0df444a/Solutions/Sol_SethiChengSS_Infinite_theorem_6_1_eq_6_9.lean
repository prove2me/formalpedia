-- Prove2me | solution 1 for SethiChengSS.Infinite.theorem_6_1_eq_6_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:39:31.89581+00:00
-- url     : https://prove2.me/submissions/f9f57ead-0dca-4469-8d7a-4b0a190f5571

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_8
import Theorems.Thm_SethiChengSS_Infinite_appendix_lipschitz

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.Eq69

open SethiChengSS.Infinite

variable {L : ℕ}

/-! ### Basic measurability, positivity, and standing-assumption helpers -/

private lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

private lemma delta_zero : delta 0 = 0 := by
  unfold delta; simp

private lemma orderCost_zero (D : Model L) (k : ℕ) (j : Fin L) :
    orderCost D k j 0 = 0 := by
  unfold orderCost; simp [delta_zero]

private lemma orderCost_nonneg {D : Model L} (hD : Standing D) {k : ℕ} {j : Fin L} {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ orderCost D k j u :=
  add_nonneg (mul_nonneg (hD.2.2.2.2.2.2.2.1 k j) (delta_nonneg u))
    (mul_nonneg (hD.2.2.2.2.2.2.2.2.1 k j) hu)

private lemma truncCost_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n : ℕ)
    (U : Policy L) (hU : ∀ t σ ξ, 0 ≤ U t σ ξ) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : 0 ≤ truncCost D α n U x σ ξ := by
  unfold truncCost
  exact Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hα _)
    (add_nonneg (orderCost_nonneg hD (hU _ _ _)) (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _))

private lemma pathWeight_nonneg {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) : 0 ≤ pathWeight D n σ ξ := by
  unfold pathWeight
  exact Finset.prod_nonneg fun k _ => mul_nonneg (hD.1 _ _) (hD.2.2.2.1 _ _ _)

private lemma continuous_of_convex_univ {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) : Continuous g := by
  have := hg.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

private lemma meas_init {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.init ξ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

private lemma meas_tail {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.tail ξ) :=
  measurable_pi_lambda _ fun a => measurable_pi_apply a.succ

private lemma meas_dmHist {m : ℕ} (t : Fin m) : Measurable (fun ξ : Fin m → ℝ => dmHist ξ t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

private lemma meas_surplus (U : Policy L) (x : ℝ) (hU : ∀ k σ, Measurable (U k σ)) :
    ∀ k, ∀ σ : Fin (k + 1) → Fin L, Measurable (surplus U x k σ) := by
  intro k
  induction k with
  | zero => intro σ; exact measurable_const
  | succ k ih =>
    intro σ
    exact (((ih _).comp meas_init).add ((hU k _).comp meas_init)).sub (measurable_pi_apply _)

private lemma meas_delta : Measurable delta := by
  unfold delta
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

private lemma meas_orderCost (D : Model L) (k : ℕ) (j : Fin L) : Measurable (orderCost D k j) := by
  unfold orderCost
  exact (measurable_const.mul meas_delta).add (measurable_const.mul measurable_id)

private lemma meas_truncCost {D : Model L} (hD : Standing D) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ)
    (hU : ∀ k σ, Measurable (U k σ)) {k : ℕ} (σ : Fin (k + 1) → Fin L) :
    Measurable (fun ξ => truncCost D α n U x σ ξ) := by
  unfold truncCost
  refine Finset.measurable_sum _ fun t _ => ?_
  exact measurable_const.mul (((meas_orderCost D _ _).comp ((hU _ _).comp (meas_dmHist t))).add
    ((continuous_of_convex_univ (hD.2.2.2.2.2.2.2.2.2.1 _ _)).measurable.comp
      ((meas_surplus U x hU _ _).comp (meas_dmHist t))))

private lemma meas_pathWeight {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) : Measurable (fun ξ : Fin t → ℝ => pathWeight D n σ ξ) := by
  unfold pathWeight
  exact Finset.measurable_prod _ fun k _ =>
    measurable_const.mul ((hD.2.2.1 _ _).comp (measurable_pi_apply _))

private lemma meas_floor : Measurable (fun x : ℝ => (⌊x⌋ : ℤ)) := by
  intro s _
  have h1 : (fun x : ℝ => (⌊x⌋ : ℤ)) ⁻¹' s = ⋃ m ∈ s, Set.Ico (m : ℝ) ((m : ℝ) + 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_Ico]
    constructor
    · intro hx
      exact ⟨⌊x⌋, hx, Int.floor_le x, Int.lt_floor_add_one x⟩
    · rintro ⟨m, hm, hlo, hhi⟩
      have : ⌊x⌋ = m := Int.floor_eq_iff.mpr ⟨hlo, hhi⟩
      rwa [this]
  rw [h1]
  exact MeasurableSet.biUnion (Set.to_countable s) fun _ _ => measurableSet_Ico

private lemma zero_adm : Admissible (zeroPolicy : Policy L) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ => measurable_const⟩

private lemma Jtrunc_zero (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    Jtrunc D α n 0 i x U = 0 := by
  unfold Jtrunc truncCost
  simp

private lemma sum_by_head {k : ℕ} (a : Fin L → ℝ≥0∞) (b : (Fin (k + 1) → Fin L) → ℝ≥0∞) :
    (∑ τ : Fin (k + 1) → Fin L, a (τ 0) * b τ) =
      ∑ j : Fin L, a j * ∑ τ : Fin (k + 1) → Fin L, if τ 0 = j then b τ else 0 := by
  calc _ = ∑ τ : Fin (k + 1) → Fin L, ∑ j : Fin L, if τ 0 = j then a j * b τ else 0 := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            simp
    _ = ∑ j : Fin L, ∑ τ : Fin (k + 1) → Fin L, if τ 0 = j then a j * b τ else 0 :=
          Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          split_ifs <;> simp

/-! ### Cons / peeling lemmas and exact one-step decomposition `Jtrunc_succ` -/

private def shiftPolicy (U : Policy L) (i : Fin L) (z : ℝ) : Policy L :=
  fun t τ η => U (t + 1) (Fin.cons i τ) (Fin.cons z η)

private lemma shiftPolicy_adm {U : Policy L} (hU : Admissible U) (i : Fin L) (z : ℝ) :
    Admissible (shiftPolicy U i z) := by
  refine ⟨fun t τ η => hU.1 _ _ _, fun t τ => ?_⟩
  have hcons : Measurable (fun η : Fin t → ℝ => (Fin.cons z η : Fin (t + 1) → ℝ)) := by
    refine measurable_pi_lambda _ fun a => ?_
    refine Fin.cases ?_ ?_ a
    · simp only [Fin.cons_zero]; exact measurable_const
    · intro b; simp only [Fin.cons_succ]; exact measurable_pi_apply b
  exact (hU.2 (t + 1) (Fin.cons i τ)).comp hcons

private lemma shiftPolicy_zero (i : Fin L) (z : ℝ) :
    shiftPolicy (zeroPolicy : Policy L) i z = zeroPolicy := rfl

private lemma init_cons {β : Type*} {m : ℕ} (a : β) (f : Fin (m + 1) → β) :
    Fin.init (Fin.cons a f : Fin (m + 2) → β) = Fin.cons a (Fin.init f) := by
  funext b
  refine Fin.cases ?_ ?_ b
  · simp [Fin.init]
  · intro c
    simp only [Fin.init, Fin.cons_succ]
    change (Fin.cons a f : Fin (m + 2) → β) c.castSucc.succ = f c.castSucc
    simp

private lemma stHist_cons_zero {k : ℕ} (i : Fin L) (τ : Fin (k + 1) → Fin L) :
    stHist (Fin.cons i τ : Fin (k + 2) → Fin L) (0 : Fin (k + 1)) = fun _ => i := by
  funext a
  have ha : a.val = 0 := by have := a.2; simp at this; omega
  have h0 : Fin.castLE (Nat.succ_le_succ (0 : Fin (k + 1)).isLt.le) a = 0 :=
    Fin.ext (by change a.val = 0; exact ha)
  simp only [stHist, h0, Fin.cons_zero]

private lemma dmHist_cons_zero {k : ℕ} (z : ℝ) (η : Fin k → ℝ) :
    dmHist (Fin.cons z η : Fin (k + 1) → ℝ) (0 : Fin (k + 1)) = Fin.elim0 := by
  funext a
  exfalso
  have := a.2
  simp at this

private lemma stHist_cons_succ {k : ℕ} (i : Fin L) (τ : Fin (k + 1) → Fin L) (t : Fin k) :
    stHist (Fin.cons i τ : Fin (k + 2) → Fin L) t.succ = Fin.cons i (stHist τ t) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [stHist]
  · intro b
    simp only [stHist, Fin.cons_succ]
    change (Fin.cons i τ : Fin (k + 2) → Fin L) (Fin.castLE (Nat.succ_le_succ t.isLt.le) b).succ = _
    simp

private lemma dmHist_cons_succ {k : ℕ} (z : ℝ) (η : Fin k → ℝ) (t : Fin k) :
    dmHist (Fin.cons z η : Fin (k + 1) → ℝ) t.succ = Fin.cons z (dmHist η t) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [dmHist]
  · intro b
    simp only [dmHist, Fin.cons_succ]
    change (Fin.cons z η : Fin (k + 1) → ℝ) (Fin.castLE t.isLt.le b).succ = _
    simp

private lemma surplus_cons (U : Policy L) (x : ℝ) (i : Fin L) (z : ℝ) :
    ∀ t (τ : Fin (t + 1) → Fin L) (η : Fin t → ℝ),
      surplus U x (t + 1) (Fin.cons i τ) (Fin.cons z η) =
        surplus (shiftPolicy U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t τ η := by
  intro t
  induction t with
  | zero =>
    intro τ η
    simp only [surplus]
    have h1 : Fin.init (Fin.cons i τ : Fin 2 → Fin L) = fun _ => i := by
      funext a; have ha : a = 0 := Subsingleton.elim _ _; subst ha; simp [Fin.init]
    have h2 : Fin.init (Fin.cons z η : Fin 1 → ℝ) = Fin.elim0 := Subsingleton.elim _ _
    have h3 : (Fin.cons z η : Fin 1 → ℝ) (Fin.last 0) = z := by simp
    rw [h1, h2, h3]
  | succ t ih =>
    intro τ η
    change surplus U x (t + 1) (Fin.init (Fin.cons i τ : Fin (t + 3) → Fin L))
          (Fin.init (Fin.cons z η : Fin (t + 2) → ℝ)) +
        U (t + 1) (Fin.init (Fin.cons i τ : Fin (t + 3) → Fin L))
          (Fin.init (Fin.cons z η : Fin (t + 2) → ℝ)) -
        (Fin.cons z η : Fin (t + 2) → ℝ) (Fin.last (t + 1)) =
      surplus (shiftPolicy U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t (Fin.init τ) (Fin.init η) +
        shiftPolicy U i z t (Fin.init τ) (Fin.init η) - η (Fin.last t)
    rw [init_cons, init_cons]
    have hlast : (Fin.cons z η : Fin (t + 2) → ℝ) (Fin.last (t + 1)) = η (Fin.last t) := by
      change (Fin.cons z η : Fin (t + 2) → ℝ) (Fin.last t).succ = η (Fin.last t)
      simp
    rw [hlast, ih]
    rfl

private lemma pathWeight_cons (D : Model L) (n : ℕ) {k : ℕ} (i : Fin L)
    (τ : Fin (k + 1) → Fin L) (z : ℝ) (η : Fin k → ℝ) :
    pathWeight D n (Fin.cons i τ : Fin (k + 2) → Fin L) (Fin.cons z η : Fin (k + 1) → ℝ) =
      (D.P i (τ 0) * D.φ n i z) * pathWeight D (n + 1) τ η := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  have h1 : (Fin.cons i τ : Fin (k + 2) → Fin L) t.succ.castSucc = τ t.castSucc := by
    change (Fin.cons i τ : Fin (k + 2) → Fin L) t.castSucc.succ = τ t.castSucc
    simp
  have h2 : (Fin.cons i τ : Fin (k + 2) → Fin L) t.succ.succ = τ t.succ := by simp
  have h3 : (Fin.cons z η : Fin (k + 1) → ℝ) t.succ = η t := by simp
  have h4 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
  rw [h1, h2, h3, h4]

private lemma truncCost_cons (D : Model L) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ) {k : ℕ}
    (i : Fin L) (τ : Fin (k + 1) → Fin L) (z : ℝ) (η : Fin k → ℝ) :
    truncCost D α n U x (Fin.cons i τ : Fin (k + 2) → Fin L) (Fin.cons z η : Fin (k + 1) → ℝ) =
      (orderCost D n i (U 0 (fun _ => i) Fin.elim0) + D.f n i x) +
      α * truncCost D α (n + 1) (shiftPolicy U i z)
        (x + U 0 (fun _ => i) Fin.elim0 - z) τ η := by
  unfold truncCost
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, add_zero, Fin.castSucc_zero, Fin.cons_zero,
      stHist_cons_zero, dmHist_cons_zero, surplus]
  · refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : (Fin.cons i τ : Fin (k + 2) → Fin L) t.succ.castSucc = τ t.castSucc := by
      change (Fin.cons i τ : Fin (k + 2) → Fin L) t.castSucc.succ = τ t.castSucc
      simp
    have h2 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
    have h3 : α ^ (t.succ : ℕ) = α * α ^ (t : ℕ) := by
      simp only [Fin.val_succ, pow_succ']
    rw [h1, h2, h3, stHist_cons_succ, dmHist_cons_succ]
    simp only [Fin.val_succ]
    rw [surplus_cons]
    simp only [shiftPolicy]
    ring

private lemma sum_cons {k : ℕ} (f : (Fin (k + 2) → Fin L) → ℝ≥0∞) (i : Fin L) :
    (∑ σ : Fin (k + 2) → Fin L, if σ 0 = i then f σ else 0) =
      ∑ τ : Fin (k + 1) → Fin L, f (Fin.cons i τ) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin L)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  rw [Finset.sum_comm]
  simp
  rfl

private lemma lintegral_cons (k : ℕ) (G : (Fin (k + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ξ : Fin (k + 1) → ℝ, G ξ ∂(Measure.pi fun _ => volume) =
      ∫⁻ z : ℝ, ∫⁻ η : Fin k → ℝ, G (Fin.cons z η) ∂(Measure.pi fun _ => volume) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have h1 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℝ))) =
      ∫⁻ ξ, G ξ ∂(Measure.pi fun _ => volume) :=
    (MeasurePreserving.symm _ hmp).lintegral_comp hG
  have h2 := lintegral_prod (μ := (volume : Measure ℝ))
    (ν := Measure.pi fun _ : Fin k => (volume : Measure ℝ))
    (f := fun p => G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p))
    (hG.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [← h1, h2]
  refine lintegral_congr fun z => lintegral_congr fun η => ?_
  congr 1
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  · intro b; simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

private lemma weight_sum {D : Model L} (hD : Standing D) :
    ∀ k n (i : Fin L),
      (∑ σ : Fin (k + 1) → Fin L, if σ 0 = i then
        ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume)
        else 0) = 1 := by
  intro k
  induction k with
  | zero =>
    intro n i
    rw [Fintype.sum_eq_single (fun _ => i)]
    · unfold pathWeight; simp
    · intro σ hσ
      rw [if_neg]
      intro h; apply hσ; funext a
      have ha : a = 0 := Fin.ext (by omega)
      subst ha; exact h
  | succ k ih =>
    intro n i
    rw [sum_cons]
    have hstep : ∀ τ : Fin (k + 1) → Fin L,
        ∫⁻ ξ : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i τ) ξ)
          ∂(Measure.pi fun _ => volume) =
        ENNReal.ofReal (D.P i (τ 0)) *
          ∫⁻ η : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) τ η)
            ∂(Measure.pi fun _ => volume) := by
      intro τ
      have hmG : Measurable (fun ξ : Fin (k + 1) → ℝ =>
          ENNReal.ofReal (pathWeight D n (Fin.cons i τ) ξ)) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)
      rw [lintegral_cons k _ hmG]
      have hm1 : Measurable (fun η : Fin k → ℝ => ENNReal.ofReal (pathWeight D (n + 1) τ η)) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) τ)
      have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (hD.2.2.1 n i)
      have he : ∀ z η, ENNReal.ofReal (pathWeight D n (Fin.cons i τ) (Fin.cons z η)) =
          (ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
            ENNReal.ofReal (pathWeight D (n + 1) τ η) := by
        intro z η
        rw [pathWeight_cons, ENNReal.ofReal_mul (mul_nonneg (hD.1 _ _) (hD.2.2.2.1 _ _ _)),
          ENNReal.ofReal_mul (hD.1 _ _)]
      simp_rw [he, lintegral_const_mul _ hm1]
      rw [lintegral_mul_const _ (hmφ.const_mul _), lintegral_const_mul _ hmφ,
        hD.2.2.2.2.2.1 n i, mul_one]
    simp_rw [hstep]
    rw [sum_by_head (fun j => ENNReal.ofReal (D.P i j))]
    simp_rw [ih (n + 1), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 i j), hD.2.1 i, ENNReal.ofReal_one]

private lemma meas_inner_Jtrunc {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (n k : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) (hU : Admissible U)
    (τ : Fin (k + 1) → Fin L) :
    Measurable (fun z : ℝ =>
      ∫⁻ η : Fin k → ℝ,
        ENNReal.ofReal (pathWeight D (n + 1) τ η) *
          ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z)
            (x + U 0 (fun _ => i) Fin.elim0 - z) τ η)
        ∂(Measure.pi fun _ => volume)) := by
  set u0 := U 0 (fun _ => i) Fin.elim0
  set c0 := orderCost D n i u0 + D.f n i x
  have hmw : Measurable (fun η : Fin k → ℝ => ENNReal.ofReal (pathWeight D (n + 1) τ η)) :=
    ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) τ)
  have hcons_m : Measurable (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine measurable_pi_lambda _ fun a => Fin.cases ?_ ?_ a
    · simp only [Fin.cons_zero]; exact measurable_fst
    · intro b; simp only [Fin.cons_succ]; exact (measurable_pi_apply b).comp measurable_snd
  have hjoint_tc : Measurable (fun p : ℝ × (Fin k → ℝ) =>
      truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u0 - p.1) τ p.2) := by
    have h1 : Measurable (fun p : ℝ × (Fin k → ℝ) =>
        (truncCost D α n U x (Fin.cons i τ) (Fin.cons p.1 p.2) - c0) / α) :=
      (((meas_truncCost hD α n U x hU.2 _).comp hcons_m).sub measurable_const).div_const α
    have heq : (fun p : ℝ × (Fin k → ℝ) =>
        truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u0 - p.1) τ p.2) =
        (fun p : ℝ × (Fin k → ℝ) =>
          (truncCost D α n U x (Fin.cons i τ) (Fin.cons p.1 p.2) - c0) / α) := by
      funext ⟨z, η⟩
      rw [truncCost_cons]
      have hne : α ≠ 0 := hα0.ne'
      dsimp only [c0, u0]
      field_simp
      ring
    rw [heq]; exact h1
  have hjoint : Measurable (fun p : ℝ × (Fin k → ℝ) =>
      ENNReal.ofReal (pathWeight D (n + 1) τ p.2) *
        ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u0 - p.1) τ p.2)) :=
    (hmw.comp measurable_snd).mul (ENNReal.measurable_ofReal.comp hjoint_tc)
  exact hjoint.lintegral_prod_right'

/-- Exact one-step decomposition of the truncated objective `Jtrunc` for any admissible policy. -/
private theorem Jtrunc_succ {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (n k : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) (hU : Admissible U) :
    Jtrunc D α n (k + 1) i x U =
      ENNReal.ofReal (D.f n i x + orderCost D n i (U 0 (fun _ => i) Fin.elim0)) +
      ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          Jtrunc D α (n + 1) k j (x + U 0 (fun _ => i) Fin.elim0 - z) (shiftPolicy U i z) := by
  set u0 := U 0 (fun _ => i) Fin.elim0
  set c0 := orderCost D n i u0 + D.f n i x
  have hc0 : 0 ≤ c0 := add_nonneg (orderCost_nonneg hD (hU.1 _ _ _)) (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _)
  have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
    ENNReal.measurable_ofReal.comp (hD.2.2.1 n i)
  unfold Jtrunc
  rw [sum_cons]
  have hτ : ∀ τ : Fin (k + 1) → Fin L,
      ∫⁻ ξ : Fin (k + 1) → ℝ,
        ENNReal.ofReal (pathWeight D n (Fin.cons i τ) ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i τ) ξ)
        ∂(Measure.pi fun _ => volume) =
      ENNReal.ofReal c0 *
        (ENNReal.ofReal (D.P i (τ 0)) *
          ∫⁻ η : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) τ η)
            ∂(Measure.pi fun _ => volume)) +
      ENNReal.ofReal α * (ENNReal.ofReal (D.P i (τ 0)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          ∫⁻ η : Fin k → ℝ,
            ENNReal.ofReal (pathWeight D (n + 1) τ η) *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)
            ∂(Measure.pi fun _ => volume)) := by
    intro τ
    have hmG : Measurable (fun ξ : Fin (k + 1) → ℝ =>
        ENNReal.ofReal (pathWeight D n (Fin.cons i τ) ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i τ) ξ)) :=
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)).mul
        (ENNReal.measurable_ofReal.comp (meas_truncCost hD α n U x hU.2 _))
    rw [lintegral_cons k _ hmG]
    have hsplit : ∀ z η,
        ENNReal.ofReal (pathWeight D n (Fin.cons i τ) (Fin.cons z η)) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i τ) (Fin.cons z η)) =
        (ENNReal.ofReal c0 * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
          ENNReal.ofReal (pathWeight D (n + 1) τ η) +
        (ENNReal.ofReal α * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
          (ENNReal.ofReal (pathWeight D (n + 1) τ η) *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)) := by
      intro z η
      rw [pathWeight_cons, truncCost_cons]
      have hw1 : 0 ≤ D.P i (τ 0) * D.φ n i z := mul_nonneg (hD.1 _ _) (hD.2.2.2.1 _ _ _)
      have htc : 0 ≤ truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η :=
        truncCost_nonneg hD hα0.le _ _ (shiftPolicy_adm hU i z).1 _ _ _
      rw [ENNReal.ofReal_mul hw1, ENNReal.ofReal_mul (hD.1 _ _),
        ENNReal.ofReal_add hc0 (mul_nonneg hα0.le htc), ENNReal.ofReal_mul hα0.le]
      ring
    simp_rw [hsplit]
    have hmw : Measurable (fun η : Fin k → ℝ => ENNReal.ofReal (pathWeight D (n + 1) τ η)) :=
      ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) τ)
    have hinner : ∀ z : ℝ,
        ∫⁻ η : Fin k → ℝ,
          ((ENNReal.ofReal c0 * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
            ENNReal.ofReal (pathWeight D (n + 1) τ η) +
          (ENNReal.ofReal α * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
            (ENNReal.ofReal (pathWeight D (n + 1) τ η) *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)))
          ∂(Measure.pi fun _ => volume) =
        (ENNReal.ofReal c0 * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
          ∫⁻ η : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) τ η)
            ∂(Measure.pi fun _ => volume) +
        (ENNReal.ofReal α * ENNReal.ofReal (D.P i (τ 0))) *
          (ENNReal.ofReal (D.φ n i z) *
            ∫⁻ η : Fin k → ℝ,
              ENNReal.ofReal (pathWeight D (n + 1) τ η) *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)
              ∂(Measure.pi fun _ => volume)) := by
      intro z
      rw [lintegral_add_left (hmw.const_mul _), lintegral_const_mul _ hmw]
      congr 1
      have hmt : Measurable (fun η : Fin k → ℝ =>
          ENNReal.ofReal (pathWeight D (n + 1) τ η) *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)) :=
        hmw.mul (ENNReal.measurable_ofReal.comp
          (meas_truncCost hD α (n + 1) (shiftPolicy U i z) (x + u0 - z)
            (shiftPolicy_adm hU i z).2 τ))
      rw [lintegral_const_mul _ hmt, mul_assoc]
    simp_rw [hinner]
    have hm_left : Measurable (fun z : ℝ =>
        (ENNReal.ofReal c0 * ENNReal.ofReal (D.P i (τ 0)) * ENNReal.ofReal (D.φ n i z)) *
          ∫⁻ η : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) τ η)
            ∂(Measure.pi fun _ => volume)) :=
      (hmφ.const_mul _).mul_const _
    rw [lintegral_add_left hm_left]
    congr 1
    · rw [lintegral_mul_const _ (hmφ.const_mul _), lintegral_const_mul _ hmφ,
        hD.2.2.2.2.2.1 n i, mul_one, mul_assoc]
    · have hm_right : Measurable (fun z : ℝ =>
          ENNReal.ofReal (D.φ n i z) *
            ∫⁻ η : Fin k → ℝ,
              ENNReal.ofReal (pathWeight D (n + 1) τ η) *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)
              ∂(Measure.pi fun _ => volume)) :=
        hmφ.mul (meas_inner_Jtrunc hD hα0 n k i x U hU τ)
      rw [lintegral_const_mul _ hm_right, mul_assoc]
  simp_rw [hτ, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum, sum_by_head (fun j => ENNReal.ofReal (D.P i j))]
    simp_rw [weight_sum hD k (n + 1), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 i j), hD.2.1 i, ENNReal.ofReal_one,
      mul_one, add_comm]
  · rw [← Finset.mul_sum, sum_by_head (fun j => ENNReal.ofReal (D.P i j))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hite : ∀ τ : Fin (k + 1) → Fin L,
        (if τ 0 = j then
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
            ∫⁻ η : Fin k → ℝ,
              ENNReal.ofReal (pathWeight D (n + 1) τ η) *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)
              ∂(Measure.pi fun _ => volume)
         else 0) =
        ∫⁻ z : ℝ, (if τ 0 = j then
          ENNReal.ofReal (D.φ n i z) *
            ∫⁻ η : Fin k → ℝ,
              ENNReal.ofReal (pathWeight D (n + 1) τ η) *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u0 - z) τ η)
              ∂(Measure.pi fun _ => volume)
         else 0) := by
      intro τ; split_ifs <;> simp
    simp_rw [hite]
    rw [← lintegral_finsetSum _ fun τ _ => by
      by_cases h : τ 0 = j
      · simp only [h, ↓reduceIte]
        exact hmφ.mul (meas_inner_Jtrunc hD hα0 n k i x U hU τ)
      · simp only [h, ↓reduceIte]; exact measurable_const]
    refine lintegral_congr fun z => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp

/-! ### Uniform linear growth bound and finiteness of `w`, `vTrunc`, `vLim` -/

private noncomputable def linConst (D : Model L) (α : ℝ) : ℝ :=
  (D.C + α * (D.C / (1 - α)) * max D.M 0) / (1 - α)

private lemma linConst_pos {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < linConst D α := by
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : 0 < 1 - α := by linarith
  have hM : 0 ≤ max D.M 0 := le_max_right _ _
  have hB : 0 < D.C / (1 - α) := div_pos hC h1
  unfold linConst
  exact div_pos (by positivity) h1

private lemma Jtrunc_zeroPolicy_le {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∀ k n (i : Fin L) (x : ℝ),
      Jtrunc D α n k i x zeroPolicy ≤ ENNReal.ofReal (linConst D α + (D.C / (1 - α)) * |x|) := by
  set M₀ := max D.M 0
  set B := D.C / (1 - α)
  set A := linConst D α
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : 0 < 1 - α := by linarith
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  have hB : 0 < B := div_pos hC h1
  have hA : 0 < A := linConst_pos hD hα0 hα1
  have hBeq : D.C + α * B = B := by
    dsimp only [B]; field_simp [h1.ne']; ring
  have hAeq : D.C + α * (A + B * M₀) = A := by
    dsimp only [A, B, M₀, linConst]; field_simp [h1.ne']; ring
  intro k
  induction k with
  | zero =>
    intro n i x
    rw [Jtrunc_zero]
    exact zero_le
  | succ k ih =>
    intro n i x
    rw [Jtrunc_succ hD hα0 n k i x zeroPolicy zero_adm]
    simp only [zeroPolicy, orderCost_zero, add_zero, shiftPolicy_zero]
    have hmean : ∫⁻ z : ℝ, ENNReal.ofReal (z * D.φ n i z) ≤ ENNReal.ofReal M₀ :=
      (hD.2.2.2.2.2.2.1 n i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hterm : ∀ j : Fin L,
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy ≤
          ENNReal.ofReal (A + B * M₀ + B * |x|) := by
      intro j
      have hpw : ∀ z : ℝ,
          ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy ≤
          ENNReal.ofReal (A + B * |x|) * ENNReal.ofReal (D.φ n i z) +
          ENNReal.ofReal B * ENNReal.ofReal (z * D.φ n i z) := by
        intro z
        by_cases hz : z < 0
        · rw [hD.2.2.2.2.1 n i z hz]; simp
        · push Not at hz
          have habs : |x - z| ≤ |x| + z := by
            calc |x - z| ≤ |x| + |z| := abs_sub _ _
              _ = |x| + z := by rw [abs_of_nonneg hz]
          have hle1 : A + B * |x - z| ≤ (A + B * |x|) + B * z := by nlinarith
          have hnn1 : 0 ≤ A + B * |x| := by positivity
          have hnn2 : 0 ≤ B * z := mul_nonneg hB.le hz
          calc ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
              ≤ ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (A + B * |x - z|) := by
                gcongr; exact ih (n + 1) j (x - z)
            _ ≤ ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal ((A + B * |x|) + B * z) := by
                gcongr
            _ = ENNReal.ofReal (D.φ n i z) *
                  (ENNReal.ofReal (A + B * |x|) + ENNReal.ofReal B * ENNReal.ofReal z) := by
                rw [ENNReal.ofReal_add hnn1 hnn2, ENNReal.ofReal_mul hB.le]
            _ = ENNReal.ofReal (A + B * |x|) * ENNReal.ofReal (D.φ n i z) +
                  ENNReal.ofReal B * (ENNReal.ofReal z * ENNReal.ofReal (D.φ n i z)) := by ring
            _ = _ := by rw [← ENNReal.ofReal_mul hz]
      have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (hD.2.2.1 n i)
      have hmzφ : Measurable (fun z : ℝ => ENNReal.ofReal (z * D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (measurable_id.mul (hD.2.2.1 n i))
      calc ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
          ≤ ∫⁻ z : ℝ, (ENNReal.ofReal (A + B * |x|) * ENNReal.ofReal (D.φ n i z) +
              ENNReal.ofReal B * ENNReal.ofReal (z * D.φ n i z)) := lintegral_mono hpw
        _ = ENNReal.ofReal (A + B * |x|) * (∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z)) +
              ENNReal.ofReal B * (∫⁻ z : ℝ, ENNReal.ofReal (z * D.φ n i z)) := by
            rw [lintegral_add_left (hmφ.const_mul _), lintegral_const_mul _ hmφ,
              lintegral_const_mul _ hmzφ]
        _ ≤ ENNReal.ofReal (A + B * |x|) * 1 + ENNReal.ofReal B * ENNReal.ofReal M₀ := by
            rw [hD.2.2.2.2.2.1 n i]; gcongr
        _ = ENNReal.ofReal (A + B * M₀ + B * |x|) := by
            rw [mul_one, ← ENNReal.ofReal_mul hB.le,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    have hf : ENNReal.ofReal (D.f n i x) ≤ ENNReal.ofReal (D.C + D.C * |x|) :=
      ENNReal.ofReal_le_ofReal (by linarith [hD.2.2.2.2.2.2.2.2.2.2.2.2.2 n i x])
    calc ENNReal.ofReal (D.f n i x) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
        ≤ ENNReal.ofReal (D.C + D.C * |x|) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ENNReal.ofReal (A + B * M₀ + B * |x|) := by
          gcongr; exact hterm _
      _ = ENNReal.ofReal (D.C + D.C * |x|) +
          ENNReal.ofReal α * ENNReal.ofReal (A + B * M₀ + B * |x|) := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 i j),
            hD.2.1 i, ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal ((D.C + α * (A + B * M₀)) + (D.C + α * B) * |x|) := by
          rw [← ENNReal.ofReal_mul hα0.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ = ENNReal.ofReal (A + B * |x|) := by rw [hAeq, hBeq]

private lemma w_le_linear {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    w D α n i x ≤ ENNReal.ofReal (linConst D α * (1 + |x|)) := by
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : 0 < 1 - α := by linarith
  have hM₀ : 0 ≤ max D.M 0 := le_max_right _ _
  have hBleA : D.C / (1 - α) ≤ linConst D α := by
    unfold linConst
    apply div_le_div_of_nonneg_right _ h1.le
    have : 0 ≤ α * (D.C / (1 - α)) * max D.M 0 := by positivity
    linarith
  have hlin : linConst D α + (D.C / (1 - α)) * |x| ≤ linConst D α * (1 + |x|) := by
    nlinarith [abs_nonneg x]
  unfold w Jinf
  exact (iSup_le fun k => Jtrunc_zeroPolicy_le hD hα0 hα1 k n i x).trans
    (ENNReal.ofReal_le_ofReal hlin)

private lemma vLim_le_w {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    vLim D α n i x ≤ w D α n i x := by
  have h68 := theorem_6_1_eq_6_8 D α hD hα0 hα1
  exact iSup_le fun k => h68.2.2 n k i x

private lemma vLim_lt_top {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    vLim D α n i x < ⊤ :=
  lt_of_le_of_lt ((vLim_le_w hD hα0 hα1 n i x).trans (w_le_linear hD hα0 hα1 n i x))
    ENNReal.ofReal_lt_top

private lemma vTrunc_lt_top {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    vTrunc D α n k i x < ⊤ :=
  lt_of_le_of_lt (le_iSup (fun k => vTrunc D α n k i x) k) (vLim_lt_top hD hα0 hα1 n i x)

private lemma vLim_toReal_le_linear {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n : ℕ) (i : Fin L) (x : ℝ) :
    (vLim D α n i x).toReal ≤ linConst D α * (1 + |x|) := by
  have hle := (vLim_le_w hD hα0 hα1 n i x).trans (w_le_linear hD hα0 hα1 n i x)
  have hpos := linConst_pos hD hα0 hα1
  calc (vLim D α n i x).toReal
      ≤ (ENNReal.ofReal (linConst D α * (1 + |x|))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = linConst D α * (1 + |x|) := ENNReal.toReal_ofReal (by positivity)

private lemma vTrunc_toReal_le_linear {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n k : ℕ) (i : Fin L) (x : ℝ) :
    (vTrunc D α n k i x).toReal ≤ linConst D α * (1 + |x|) := by
  have hle : vTrunc D α n k i x ≤ vLim D α n i x := le_iSup (fun k => vTrunc D α n k i x) k
  exact (ENNReal.toReal_mono (vLim_lt_top hD hα0 hα1 n i x).ne hle).trans
    (vLim_toReal_le_linear hD hα0 hα1 n i x)

/-! ### Properties of the operator `Fnext` -/

private lemma integrable_phi {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L) :
    Integrable (D.φ n i) volume := by
  refine ⟨(hD.2.2.1 n i).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have h1 : ∀ z, ‖D.φ n i z‖ₑ = ENNReal.ofReal (D.φ n i z) := fun z => by
    rw [Real.enorm_eq_ofReal (hD.2.2.2.1 n i z)]
  simp_rw [h1, hD.2.2.2.2.2.1 n i]
  exact ENNReal.one_lt_top

private lemma abs_mul_phi_eq {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L) (z : ℝ) :
    |z| * D.φ n i z = z * D.φ n i z := by
  by_cases hz : z < 0
  · rw [hD.2.2.2.2.1 n i z hz]; ring
  · push Not at hz; rw [abs_of_nonneg hz]

private lemma integrable_abs_mul_phi {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L) :
    Integrable (fun z => |z| * D.φ n i z) volume := by
  refine ⟨(continuous_abs.measurable.mul (hD.2.2.1 n i)).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have h1 : ∀ z, ‖|z| * D.φ n i z‖ₑ = ENNReal.ofReal (z * D.φ n i z) := fun z => by
    rw [Real.enorm_eq_ofReal (mul_nonneg (abs_nonneg z) (hD.2.2.2.1 n i z)),
      abs_mul_phi_eq hD n i z]
  simp_rw [h1]
  exact lt_of_le_of_lt (hD.2.2.2.2.2.2.1 n i) ENNReal.ofReal_lt_top

private lemma setIntegral_Ioi_eq_integral_of_phi {D : Model L} (hD : Standing D) (n : ℕ)
    (i : Fin L) (g : ℝ → ℝ) :
    ∫ z in Set.Ioi (0 : ℝ), g z * D.φ n i z = ∫ z, g z * D.φ n i z := by
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  have h0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with z hz hnot
  have hlt : z < 0 := lt_of_le_of_ne (not_lt.mp hnot) hz
  rw [hD.2.2.2.2.1 n i z hlt, mul_zero]

private lemma integral_phi_Ioi {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi (0 : ℝ), D.φ n i z = 1 := by
  have heq : ∫ z in Set.Ioi (0 : ℝ), D.φ n i z = ∫ z, D.φ n i z := by
    simpa using setIntegral_Ioi_eq_integral_of_phi hD n i (fun _ => 1)
  rw [heq]
  have hnn : 0 ≤ᵐ[volume] D.φ n i := Eventually.of_forall (hD.2.2.2.1 n i)
  have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_phi hD n i) hnn
  rw [hD.2.2.2.2.2.1 n i] at h1
  have hnn_int : 0 ≤ ∫ z, D.φ n i z := integral_nonneg (hD.2.2.2.1 n i)
  have h2 := congr_arg ENNReal.toReal h1
  rw [ENNReal.toReal_ofReal hnn_int, ENNReal.toReal_one] at h2
  exact h2

private lemma integrable_Fnext_term {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L)
    (b : Fin L → ℝ → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb) (hbm : ∀ j, Measurable (b j))
    (hb0 : ∀ j y, 0 ≤ b j y) (hbgr : ∀ j y, b j y ≤ Cb * (1 + |y|)) (j : Fin L) (y : ℝ) :
    Integrable (fun z => b j (y - z) * D.φ n i z) volume := by
  have hdom : Integrable (fun z => (Cb * (1 + |y|)) * D.φ n i z + Cb * (|z| * D.φ n i z)) volume :=
    ((integrable_phi hD n i).const_mul _).add ((integrable_abs_mul_phi hD n i).const_mul _)
  refine hdom.mono' (((hbm j).comp (measurable_const.sub measurable_id)).mul
    (hD.2.2.1 n i)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  have hnn : 0 ≤ b j (y - z) * D.φ n i z := mul_nonneg (hb0 j _) (hD.2.2.2.1 n i z)
  rw [Real.norm_of_nonneg hnn]
  have habs : |y - z| ≤ |y| + |z| := abs_sub _ _
  have hφ := hD.2.2.2.1 n i z
  have h1 : b j (y - z) ≤ Cb * (1 + |y|) + Cb * |z| := by
    calc b j (y - z) ≤ Cb * (1 + |y - z|) := hbgr j (y - z)
      _ ≤ Cb * (1 + (|y| + |z|)) := by nlinarith
      _ = Cb * (1 + |y|) + Cb * |z| := by ring
  nlinarith

private lemma Fnext_nonneg {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hb0 : ∀ j y, 0 ≤ b j y) (i : Fin L) (y : ℝ) : 0 ≤ Fnext D n b i y := by
  unfold Fnext
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hD.1 i j) ?_
  exact integral_nonneg fun z => mul_nonneg (hb0 j _) (hD.2.2.2.1 n i z)

private lemma ofReal_Fnext {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (Cb : ℝ) (hCb : 0 ≤ Cb) (hbm : ∀ j, Measurable (b j))
    (hb0 : ∀ j y, 0 ≤ b j y) (hbgr : ∀ j y, b j y ≤ Cb * (1 + |y|)) (i : Fin L) (y : ℝ) :
    ENNReal.ofReal (Fnext D n b i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (y - z)) := by
  unfold Fnext
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (hD.1 i j) (integral_nonneg fun z => mul_nonneg (hb0 j _) (hD.2.2.2.1 n i z))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (hD.1 i j), setIntegral_Ioi_eq_integral_of_phi hD n i (fun z => b j (y - z))]
  congr 1
  have hint := integrable_Fnext_term hD n i b Cb hCb hbm hb0 hbgr j y
  have hnn : 0 ≤ᵐ[volume] fun z => b j (y - z) * D.φ n i z :=
    Eventually.of_forall fun z => mul_nonneg (hb0 j _) (hD.2.2.2.1 n i z)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr fun z => ?_
  rw [mul_comm, ENNReal.ofReal_mul (hD.2.2.2.1 n i z)]

private lemma Fnext_mono {D : Model L} (hD : Standing D) (n : ℕ)
    (b₁ b₂ : Fin L → ℝ → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hm₁ : ∀ j, Measurable (b₁ j)) (h0₁ : ∀ j y, 0 ≤ b₁ j y) (hg₁ : ∀ j y, b₁ j y ≤ Cb * (1 + |y|))
    (hm₂ : ∀ j, Measurable (b₂ j)) (h0₂ : ∀ j y, 0 ≤ b₂ j y) (hg₂ : ∀ j y, b₂ j y ≤ Cb * (1 + |y|))
    (hle : ∀ j y, b₁ j y ≤ b₂ j y) (i : Fin L) (y : ℝ) :
    Fnext D n b₁ i y ≤ Fnext D n b₂ i y := by
  unfold Fnext
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hD.1 i j)
  refine integral_mono
    (integrable_Fnext_term hD n i b₁ Cb hCb hm₁ h0₁ hg₁ j y).integrableOn
    (integrable_Fnext_term hD n i b₂ Cb hCb hm₂ h0₂ hg₂ j y).integrableOn ?_
  intro z
  exact mul_le_mul_of_nonneg_right (hle j (y - z)) (hD.2.2.2.1 n i z)

private lemma Fnext_lip {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (Cb L_lip : ℝ) (hCb : 0 ≤ Cb) (hbm : ∀ j, Measurable (b j))
    (hb0 : ∀ j y, 0 ≤ b j y) (hbgr : ∀ j y, b j y ≤ Cb * (1 + |y|))
    (hlip : ∀ j y y', |b j y' - b j y| ≤ L_lip * |y' - y|) (i : Fin L) (y y' : ℝ) :
    |Fnext D n b i y' - Fnext D n b i y| ≤ L_lip * |y' - y| := by
  unfold Fnext
  rw [← Finset.sum_sub_distrib]
  calc |∑ j : Fin L, ((D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y' - z) * D.φ n i z) -
            (D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z))|
      ≤ ∑ j : Fin L, |(D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y' - z) * D.φ n i z) -
            (D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin L, D.P i j * (L_lip * |y' - y|) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hD.1 i j)]
        refine mul_le_mul_of_nonneg_left ?_ (hD.1 i j)
        have h1 := (integrable_Fnext_term hD n i b Cb hCb hbm hb0 hbgr j y').integrableOn
          (s := Set.Ioi (0 : ℝ))
        have h2 := (integrable_Fnext_term hD n i b Cb hCb hbm hb0 hbgr j y).integrableOn
          (s := Set.Ioi (0 : ℝ))
        rw [← integral_sub h1 h2]
        calc |∫ z in Set.Ioi (0 : ℝ), (b j (y' - z) * D.φ n i z - b j (y - z) * D.φ n i z)|
            ≤ ∫ z in Set.Ioi (0 : ℝ), |b j (y' - z) * D.φ n i z - b j (y - z) * D.φ n i z| := by
              simpa [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (0 : ℝ)))
                  (f := fun z => b j (y' - z) * D.φ n i z - b j (y - z) * D.φ n i z)
          _ ≤ ∫ z in Set.Ioi (0 : ℝ), (L_lip * |y' - y|) * D.φ n i z := by
              refine integral_mono (h1.sub h2).norm
                ((integrable_phi hD n i).integrableOn.const_mul _) fun z => ?_
              rw [← sub_mul, abs_mul, abs_of_nonneg (hD.2.2.2.1 n i z)]
              refine mul_le_mul_of_nonneg_right ?_ (hD.2.2.2.1 n i z)
              have := hlip j (y - z) (y' - z)
              have he : y' - z - (y - z) = y' - y := by ring
              rwa [he] at this
          _ = L_lip * |y' - y| := by
              rw [integral_const_mul, integral_phi_Ioi hD n i, mul_one]
    _ = L_lip * |y' - y| := by
        rw [← Finset.sum_mul, hD.2.1 i, one_mul]

private lemma continuous_of_lip {g : ℝ → ℝ} {L_lip : ℝ} (hL : 0 ≤ L_lip)
    (hlip : ∀ y y', |g y' - g y| ≤ L_lip * |y' - y|) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (L_lip + 1), div_pos hε (by linarith), fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |g y - g x| ≤ L_lip * |y - x| := hlip x y
    _ ≤ (L_lip + 1) * |y - x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (L_lip + 1) * (ε / (L_lip + 1)) := mul_lt_mul_of_pos_left hy (by linarith)
    _ = ε := mul_div_cancel₀ ε (by linarith)

private lemma Fnext_tendsto {D : Model L} (hD : Standing D) (n : ℕ)
    (bk : ℕ → Fin L → ℝ → ℝ) (b : Fin L → ℝ → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hmk : ∀ k j, Measurable (bk k j)) (h0k : ∀ k j y, 0 ≤ bk k j y)
    (hgk : ∀ k j y, bk k j y ≤ Cb * (1 + |y|))
    (hlim : ∀ j y, Tendsto (fun k => bk k j y) atTop (𝓝 (b j y)))
    (i : Fin L) (y : ℝ) :
    Tendsto (fun k => Fnext D n (bk k) i y) atTop (𝓝 (Fnext D n b i y)) := by
  unfold Fnext
  refine tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul ?_
  have hbound : IntegrableOn (fun z => (Cb * (1 + |y|)) * D.φ n i z + Cb * (|z| * D.φ n i z))
      (Set.Ioi (0 : ℝ)) volume :=
    (((integrable_phi hD n i).const_mul _).add ((integrable_abs_mul_phi hD n i).const_mul _)).integrableOn
  refine tendsto_integral_of_dominated_convergence
    (fun z => (Cb * (1 + |y|)) * D.φ n i z + Cb * (|z| * D.φ n i z))
    (fun k => (((hmk k j).comp (measurable_const.sub measurable_id)).mul
      (hD.2.2.1 n i)).aestronglyMeasurable)
    hbound
    (fun k => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => (hlim j (y - z)).mul_const _)
  have hnn : 0 ≤ bk k j (y - z) * D.φ n i z := mul_nonneg (h0k k j _) (hD.2.2.2.1 n i z)
  rw [Real.norm_of_nonneg hnn]
  have habs : |y - z| ≤ |y| + |z| := abs_sub _ _
  have hφ := hD.2.2.2.1 n i z
  have h1 : bk k j (y - z) ≤ Cb * (1 + |y|) + Cb * |z| := by
    calc bk k j (y - z) ≤ Cb * (1 + |y - z|) := hgk k j (y - z)
      _ ≤ Cb * (1 + (|y| + |z|)) := by nlinarith
      _ = Cb * (1 + |y|) + Cb * |z| := by ring
  nlinarith

/-! ### Uniform shift bound `Jtrunc_shift` (for discretizing in `z`) -/

private lemma surplus_shift (U : Policy L) (x x' : ℝ) :
    ∀ t (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ),
      surplus U x' t σ ξ = surplus U x t σ ξ + (x' - x) := by
  intro t
  induction t with
  | zero => intro σ ξ; simp only [surplus]; ring
  | succ t ih => intro σ ξ; simp only [surplus, ih]; ring

private lemma f_lipschitz {D : Model L} (hD : Standing D) (k : ℕ) (j : Fin L) (a b : ℝ) :
    D.f k j b - D.f k j a ≤ D.C * |b - a| := by
  have hconv := hD.2.2.2.2.2.2.2.2.2.1 k j
  have hnn := hD.2.2.2.2.2.2.2.2.2.2.1 k j
  have hgr := hD.2.2.2.2.2.2.2.2.2.2.2.2.2 k j
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases lt_trichotomy a b with hab | hab | hab
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (b - a) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := a) (y := b) (z := b + t) trivial trivial hab
        (by linarith)
      have e1 : b + t - b = t := by ring
      rw [e1] at hs
      have h1 : (D.f k j b - D.f k j a) ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := by
        rw [div_le_iff₀ (by linarith)] at hs
        rw [mul_comm]; exact hs
      have h2 : (D.f k j (b + t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b + t); have := hnn b
        have : |b + t| ≤ |b| + t := by
          calc |b + t| ≤ |b| + |t| := abs_add_le _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hlim : Tendsto (fun t : ℝ => (b - a) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((b - a) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht => hkey t ht)
    rw [abs_of_pos (by linarith : 0 < b - a)]
    linarith
  · subst hab; simp
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (a - b) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := b - t) (y := b) (z := a) trivial trivial
        (by linarith) hab
      have e1 : b - (b - t) = t := by ring
      rw [e1] at hs
      have h1 : D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := by
        have h3 : (D.f k j b - D.f k j (b - t)) / t * (a - b) ≤ D.f k j a - D.f k j b := by
          have := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ a - b)
          rwa [div_mul_cancel₀ _ (by linarith : (a - b) ≠ 0)] at this
        have e : (a - b) * ((D.f k j (b - t) - D.f k j b) / t) =
            -((D.f k j b - D.f k j (b - t)) / t * (a - b)) := by ring
        rw [e]; linarith
      have h2 : (D.f k j (b - t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b - t); have := hnn b
        have : |b - t| ≤ |b| + t := by
          calc |b - t| ≤ |b| + |t| := abs_sub _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hlim : Tendsto (fun t : ℝ => (a - b) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((a - b) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht => hkey t ht)
    rw [abs_of_neg (by linarith : b - a < 0)]
    linarith

private lemma geom_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∑ t : Fin k, α ^ (t : ℕ) ≤ 1 / (1 - α) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => α ^ t), geom_sum_eq hα1.ne]
  have h1 : 0 < 1 - α := by linarith
  have e : (α ^ k - 1) / (α - 1) = (1 - α ^ k) / (1 - α) := by
    have hne1 : α - 1 ≠ 0 := by linarith
    have hne2 : 1 - α ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ h1.le
  have := pow_nonneg hα0.le k
  linarith

private lemma truncCost_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (U : Policy L) (x x' : ℝ) {k : ℕ} (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) :
    truncCost D α n U x' σ ξ ≤ truncCost D α n U x σ ξ + D.C * |x' - x| / (1 - α) := by
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold truncCost
  have hterm : ∀ t : Fin k,
      α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
        D.f (n + t) (σ t.castSucc) (surplus U x' t (stHist σ t) (dmHist ξ t))) ≤
      α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
        D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))) +
      α ^ (t : ℕ) * (D.C * |x' - x|) := by
    intro t
    rw [surplus_shift U x x']
    have := f_lipschitz hD (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))
      (surplus U x t (stHist σ t) (dmHist ξ t) + (x' - x))
    have e : surplus U x t (stHist σ t) (dmHist ξ t) + (x' - x) -
        surplus U x t (stHist σ t) (dmHist ξ t) = x' - x := by ring
    rw [e] at this
    have hp := pow_nonneg hα0.le (t : ℕ)
    nlinarith
  calc _ ≤ ∑ t : Fin k, (α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc)
          (U t (stHist σ t) (dmHist ξ t)) +
          D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))) +
        α ^ (t : ℕ) * (D.C * |x' - x|)) := Finset.sum_le_sum fun t _ => hterm t
    _ = _ + (∑ t : Fin k, α ^ (t : ℕ)) * (D.C * |x' - x|) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := by
        have hg := geom_le hα0 hα1 k
        have h2 := mul_le_mul_of_nonneg_right hg (by positivity : 0 ≤ D.C * |x' - x|)
        have e : 1 / (1 - α) * (D.C * |x' - x|) = D.C * |x' - x| / (1 - α) := by ring
        linarith

private lemma Jtrunc_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x x' : ℝ) (U : Policy L) :
    Jtrunc D α n k i x' U ≤
      Jtrunc D α n k i x U + ENNReal.ofReal (D.C * |x' - x| / (1 - α)) := by
  set B := D.C * |x' - x| / (1 - α)
  unfold Jtrunc
  calc _ ≤ ∑ σ : Fin (k + 1) → Fin L, ((if σ 0 = i then
        ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) *
          ENNReal.ofReal (truncCost D α n U x σ ξ) ∂(Measure.pi fun _ => volume) else 0) +
        ENNReal.ofReal B * (if σ 0 = i then
          ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume)
          else 0)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with hσ
        · have hmw : Measurable (fun ξ : Fin k → ℝ => ENNReal.ofReal (pathWeight D n σ ξ)) :=
            ENNReal.measurable_ofReal.comp (meas_pathWeight hD n σ)
          rw [← lintegral_const_mul _ hmw, ← lintegral_add_right _ (hmw.const_mul _)]
          refine lintegral_mono fun ξ => ?_
          have h1 := ENNReal.ofReal_le_ofReal (truncCost_shift hD hα0 hα1 n U x x' σ ξ)
          have h2 := ENNReal.ofReal_add_le (p := truncCost D α n U x σ ξ) (q := B)
          calc ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (truncCost D α n U x' σ ξ)
              ≤ ENNReal.ofReal (pathWeight D n σ ξ) *
                  (ENNReal.ofReal (truncCost D α n U x σ ξ) + ENNReal.ofReal B) := by
                gcongr; exact h1.trans h2
            _ = _ := by ring
        · simp
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, weight_sum hD k n i, mul_one]

/-! ### Truncated DP equation (6.5) for `(vTrunc D α n k i x).toReal` -/

private lemma Jtrunc_congr_of_head {D : Model L} (α : ℝ) (n k : ℕ) (j : Fin L) (y : ℝ)
    (U₁ U₂ : Policy L) (h : ∀ t (τ : Fin (t + 1) → Fin L) η, τ 0 = j → U₁ t τ η = U₂ t τ η) :
    Jtrunc D α n k j y U₁ = Jtrunc D α n k j y U₂ := by
  have hsurp : ∀ t (τ : Fin (t + 1) → Fin L) η, τ 0 = j →
      surplus U₁ y t τ η = surplus U₂ y t τ η := by
    intro t
    induction t with
    | zero => intro τ η _; rfl
    | succ t ih =>
      intro τ η hτ
      have h0 : Fin.init τ 0 = j := hτ
      simp only [surplus, ih _ _ h0, h t _ _ h0]
  unfold Jtrunc
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs with hτ
  · refine lintegral_congr fun η => ?_
    congr 2
    unfold truncCost
    refine Finset.sum_congr rfl fun t _ => ?_
    have h0 : stHist τ t 0 = j := hτ
    rw [h t _ _ h0, hsurp t _ _ h0]
  · rfl

private noncomputable def gluePolicy (u δ : ℝ) (W : Fin L → ℤ → Policy L) : Policy L
  | 0, _, _ => u
  | t + 1, σ, ξ => W (σ 1) ⌊ξ 0 / δ⌋ t (Fin.tail σ) (Fin.tail ξ)

private lemma gluePolicy_adm {u δ : ℝ} (hu : 0 ≤ u) (W : Fin L → ℤ → Policy L)
    (hW : ∀ j m, Admissible (W j m)) : Admissible (gluePolicy u δ W) := by
  refine ⟨fun t σ ξ => ?_, fun t σ => ?_⟩
  · cases t with
    | zero => exact hu
    | succ t => exact (hW _ _).1 _ _ _
  · cases t with
    | zero => exact measurable_const
    | succ t =>
      have h0 : Measurable (fun ξ : Fin (t + 1) → ℝ => ξ 0 / δ) :=
        (measurable_pi_apply (0 : Fin (t + 1)) :
          Measurable (fun ξ : Fin (t + 1) → ℝ => ξ 0)).div_const δ
      have hpair : Measurable (fun ξ : Fin (t + 1) → ℝ => (⌊ξ 0 / δ⌋, Fin.tail ξ)) :=
        (meas_floor.comp h0).prodMk meas_tail
      have hfn : Measurable (fun p : ℤ × (Fin t → ℝ) => W (σ 1) p.1 t (Fin.tail σ) p.2) :=
        measurable_from_prod_countable_right fun m => (hW (σ 1) m).2 t (Fin.tail σ)
      exact hfn.comp hpair

private lemma vTrunc_toReal_continuous {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n k : ℕ) (j : Fin L) :
    Continuous (fun y => (vTrunc D α n k j y).toReal) := by
  have hlip := (appendix_lipschitz D α hD hα0 hα1).1 n k j
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hL : 0 ≤ D.C / (1 - α) := div_nonneg hC.le (by linarith)
  refine continuous_of_lip hL fun y y' => ?_
  calc |(vTrunc D α n k j y').toReal - (vTrunc D α n k j y).toReal|
      ≤ D.C * |y' - y| / (1 - α) := hlip y y'
    _ = D.C / (1 - α) * |y' - y| := by ring

private lemma vLim_toReal_continuous {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n : ℕ) (j : Fin L) :
    Continuous (fun y => (vLim D α n j y).toReal) := by
  have hlip := (appendix_lipschitz D α hD hα0 hα1).2 n j
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hL : 0 ≤ D.C / (1 - α) := div_nonneg hC.le (by linarith)
  refine continuous_of_lip hL fun y y' => ?_
  calc |(vLim D α n j y').toReal - (vLim D α n j y).toReal|
      ≤ D.C * |y' - y| / (1 - α) := hlip y y'
    _ = D.C / (1 - α) * |y' - y| := by ring

private lemma dp_bddBelow {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (n : ℕ) (b : Fin L → ℝ → ℝ) (hb0 : ∀ j y, 0 ≤ b j y) (i : Fin L) (x : ℝ) :
    BddBelow (Set.range fun u : {u : ℝ // 0 ≤ u} =>
      orderCost D n i u.1 + α * Fnext D n b i (x + u.1)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact add_nonneg (orderCost_nonneg hD u.2) (mul_nonneg hα0.le (Fnext_nonneg hD n b hb0 i _))

private lemma vTrunc_dp {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    (vTrunc D α n (k + 1) i x).toReal =
      D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u.1 +
          α * Fnext D n (fun j y => (vTrunc D α (n + 1) k j y).toReal) i (x + u.1)) := by
  set V : Fin L → ℝ → ℝ := fun j y => (vTrunc D α (n + 1) k j y).toReal
  have hV0 : ∀ j y, 0 ≤ V j y := fun j y => ENNReal.toReal_nonneg
  have hVm : ∀ j, Measurable (V j) := fun j => (vTrunc_toReal_continuous hD hα0 hα1 (n + 1) k j).measurable
  have hVgr : ∀ j y, V j y ≤ linConst D α * (1 + |y|) :=
    fun j y => vTrunc_toReal_le_linear hD hα0 hα1 (n + 1) k j y
  have hApos := linConst_pos hD hα0 hα1
  have hbdd := dp_bddBelow hD hα0 n V hV0 i x
  have hF_ofReal : ∀ y, ENNReal.ofReal (Fnext D n V i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z) := by
    intro y
    rw [ofReal_Fnext hD n V (linConst D α) hApos.le hVm hV0 hVgr i y]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_toReal (vTrunc_lt_top hD hα0 hα1 (n + 1) k j (y - z)).ne]
  apply le_antisymm
  · -- Direction `≤`: fix `u ≥ 0` and approximate with piecewise-constant policies in `z`.
    have hle_u : ∀ u : {u : ℝ // 0 ≤ u},
        (vTrunc D α n (k + 1) i x).toReal - D.f n i x ≤
          orderCost D n i u.1 + α * Fnext D n V i (x + u.1) := by
      intro u
      suffices h : ∀ ε : ℝ, 0 < ε →
          (vTrunc D α n (k + 1) i x).toReal ≤
            D.f n i x + orderCost D n i u.1 + α * Fnext D n V i (x + u.1) + ε by
        by_contra hlt
        push Not at hlt
        set gap := ((vTrunc D α n (k + 1) i x).toReal - D.f n i x) -
          (orderCost D n i u.1 + α * Fnext D n V i (x + u.1))
        have hgap : 0 < gap := sub_pos.mpr hlt
        have := h (gap / 2) (half_pos hgap)
        linarith
      intro ε hε
      have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
      set L_lip := D.C / (1 - α)
      have hLpos : 0 < L_lip := div_pos hC (by linarith)
      set ε₁ := ε / (2 * α)
      have hε₁ : 0 < ε₁ := div_pos hε (by linarith)
      set δ := ε / (4 * α * L_lip)
      have hδ : 0 < δ := div_pos hε (by positivity)
      -- For each j and m : ℤ, pick an ε₁-optimal admissible policy at y_m = x + u - m * δ
      have hex : ∀ (j : Fin L) (m : ℤ), ∃ U : Policy L, Admissible U ∧
          Jtrunc D α (n + 1) k j (x + u.1 - (m : ℝ) * δ) U ≤
            vTrunc D α (n + 1) k j (x + u.1 - (m : ℝ) * δ) + ENNReal.ofReal ε₁ := by
        intro j m
        set ym := x + u.1 - (m : ℝ) * δ
        have hlt_top := vTrunc_lt_top hD hα0 hα1 (n + 1) k j ym
        have hlt : vTrunc D α (n + 1) k j ym < vTrunc D α (n + 1) k j ym + ENNReal.ofReal ε₁ :=
          ENNReal.lt_add_right hlt_top.ne (ENNReal.ofReal_pos.mpr hε₁).ne'
        unfold vTrunc at hlt
        rw [iInf_lt_iff] at hlt
        obtain ⟨U, hU⟩ := hlt
        rw [iInf_lt_iff] at hU
        obtain ⟨hUadm, hUle⟩ := hU
        exact ⟨U, hUadm, hUle.le⟩
      choose W hWadm hWle using hex
      set U := gluePolicy u.1 δ W
      have hUadm : Admissible U := gluePolicy_adm u.2 W hWadm
      have hJ_bound : Jtrunc D α n (k + 1) i x U ≤
          ENNReal.ofReal (D.f n i x + orderCost D n i u.1 + α * Fnext D n V i (x + u.1) + ε) := by
        rw [Jtrunc_succ hD hα0 n k i x U hUadm]
        have hu0 : U 0 (fun _ => i) Fin.elim0 = u.1 := rfl
        rw [hu0]
        -- Bound each Jtrunc (n+1) k j (x + u - z) (shiftPolicy U i z)
        have hpt : ∀ (j : Fin L) (z : ℝ),
            Jtrunc D α (n + 1) k j (x + u.1 - z) (shiftPolicy U i z) ≤
              vTrunc D α (n + 1) k j (x + u.1 - z) + ENNReal.ofReal (ε / α) := by
          intro j z
          set m : ℤ := ⌊z / δ⌋
          have hagree : Jtrunc D α (n + 1) k j (x + u.1 - z) (shiftPolicy U i z) =
              Jtrunc D α (n + 1) k j (x + u.1 - z) (W j m) := by
            refine Jtrunc_congr_of_head α (n + 1) k j (x + u.1 - z) _ _ ?_
            intro t τ η hτ
            change W ((Fin.cons i τ : Fin (t + 2) → Fin L) 1) ⌊(Fin.cons z η : Fin (t + 1) → ℝ) 0 / δ⌋
              t (Fin.tail (Fin.cons i τ : Fin (t + 2) → Fin L))
              (Fin.tail (Fin.cons z η : Fin (t + 1) → ℝ)) = W j m t τ η
            have h1 : (Fin.cons i τ : Fin (t + 2) → Fin L) 1 = j := by
              change (Fin.cons i τ : Fin (t + 2) → Fin L) (0 : Fin (t + 1)).succ = j
              simp [hτ]
            rw [h1, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons]
          rw [hagree]
          set ym := x + u.1 - (m : ℝ) * δ
          have hdiff : |(x + u.1 - z) - ym| ≤ δ := by
            have hlo : (m : ℝ) ≤ z / δ := Int.floor_le (z / δ)
            have hhi : z / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (z / δ)
            have hlo' : (m : ℝ) * δ ≤ z := (le_div_iff₀ hδ).mp hlo
            have hhi' : z < ((m : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hhi
            have he : (x + u.1 - z) - ym = (m : ℝ) * δ - z := by dsimp only [ym]; ring
            rw [he, abs_le]
            constructor <;> linarith
          have hshift_J := Jtrunc_shift hD hα0 hα1 (n + 1) k j ym (x + u.1 - z) (W j m)
          have hlip_v : vTrunc D α (n + 1) k j ym ≤
              vTrunc D α (n + 1) k j (x + u.1 - z) + ENNReal.ofReal (L_lip * δ) := by
            have hv1 := (appendix_lipschitz D α hD hα0 hα1).1 (n + 1) k j (x + u.1 - z) ym
            rw [abs_le] at hv1
            have hdiff' : |ym - (x + u.1 - z)| ≤ δ := by rwa [abs_sub_comm]
            have hle_real : (vTrunc D α (n + 1) k j ym).toReal ≤
                (vTrunc D α (n + 1) k j (x + u.1 - z)).toReal + L_lip * δ := by
              have h1 : D.C * |ym - (x + u.1 - z)| / (1 - α) ≤ L_lip * δ := by
                dsimp only [L_lip]
                rw [mul_div_right_comm]
                exact mul_le_mul_of_nonneg_left hdiff' (div_nonneg hC.le (by linarith))
              linarith
            rw [← ENNReal.ofReal_toReal (vTrunc_lt_top hD hα0 hα1 (n + 1) k j ym).ne,
              ← ENNReal.ofReal_toReal (vTrunc_lt_top hD hα0 hα1 (n + 1) k j (x + u.1 - z)).ne,
              ← ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hLpos.le hδ.le)]
            exact ENNReal.ofReal_le_ofReal hle_real
          have hB_le : D.C * |(x + u.1 - z) - ym| / (1 - α) ≤ L_lip * δ := by
            dsimp only [L_lip]
            rw [mul_div_right_comm]
            exact mul_le_mul_of_nonneg_left hdiff (div_nonneg hC.le (by linarith))
          have hsum_eps : L_lip * δ + ε₁ + L_lip * δ = ε / α := by
            dsimp only [ε₁, δ]
            have hneα : α ≠ 0 := hα0.ne'
            have hneL : L_lip ≠ 0 := hLpos.ne'
            field_simp; ring
          calc Jtrunc D α (n + 1) k j (x + u.1 - z) (W j m)
              ≤ Jtrunc D α (n + 1) k j ym (W j m) + ENNReal.ofReal (L_lip * δ) := by
                calc Jtrunc D α (n + 1) k j (x + u.1 - z) (W j m)
                    ≤ Jtrunc D α (n + 1) k j ym (W j m) +
                        ENNReal.ofReal (D.C * |(x + u.1 - z) - ym| / (1 - α)) := hshift_J
                  _ ≤ _ := by gcongr
            _ ≤ (vTrunc D α (n + 1) k j ym + ENNReal.ofReal ε₁) + ENNReal.ofReal (L_lip * δ) := by
                gcongr; exact hWle j m
            _ ≤ ((vTrunc D α (n + 1) k j (x + u.1 - z) + ENNReal.ofReal (L_lip * δ)) +
                  ENNReal.ofReal ε₁) + ENNReal.ofReal (L_lip * δ) := by gcongr
            _ = vTrunc D α (n + 1) k j (x + u.1 - z) +
                  ENNReal.ofReal (L_lip * δ + ε₁ + L_lip * δ) := by
                rw [add_assoc, add_assoc, ← ENNReal.ofReal_add hε₁.le (by positivity),
                  ← ENNReal.ofReal_add (by positivity) (by positivity)]
                congr 2; ring
            _ = vTrunc D α (n + 1) k j (x + u.1 - z) + ENNReal.ofReal (ε / α) := by rw [hsum_eps]
        have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
          ENNReal.measurable_ofReal.comp (hD.2.2.1 n i)
        have hsum_j : ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
              Jtrunc D α (n + 1) k j (x + u.1 - z) (shiftPolicy U i z) ≤
            ENNReal.ofReal (Fnext D n V i (x + u.1)) + ENNReal.ofReal (ε / α) := by
          calc _ ≤ ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
                ((∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u.1 - z)) +
                  ENNReal.ofReal (ε / α)) := by
                refine Finset.sum_le_sum fun j _ => ?_
                gcongr
                calc ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
                        Jtrunc D α (n + 1) k j (x + u.1 - z) (shiftPolicy U i z)
                    ≤ ∫⁻ z : ℝ, (ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u.1 - z) +
                        ENNReal.ofReal (ε / α) * ENNReal.ofReal (D.φ n i z)) := by
                      refine lintegral_mono fun z => ?_
                      calc _ ≤ ENNReal.ofReal (D.φ n i z) *
                              (vTrunc D α (n + 1) k j (x + u.1 - z) + ENNReal.ofReal (ε / α)) := by
                            gcongr; exact hpt j z
                        _ = _ := by ring
                  _ = _ := by
                      rw [lintegral_add_right _ (hmφ.const_mul _), lintegral_const_mul _ hmφ,
                        hD.2.2.2.2.2.1 n i, mul_one]
            _ = (∑ j : Fin L, ENNReal.ofReal (D.P i j) *
                  ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u.1 - z)) +
                (∑ j : Fin L, ENNReal.ofReal (D.P i j)) * ENNReal.ofReal (ε / α) := by
                simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
            _ = ENNReal.ofReal (Fnext D n V i (x + u.1)) + ENNReal.ofReal (ε / α) := by
                rw [← hF_ofReal (x + u.1),
                  ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 i j), hD.2.1 i,
                  ENNReal.ofReal_one, one_mul]
        calc ENNReal.ofReal (D.f n i x + orderCost D n i u.1) +
              ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
                ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
                  Jtrunc D α (n + 1) k j (x + u.1 - z) (shiftPolicy U i z)
            ≤ ENNReal.ofReal (D.f n i x + orderCost D n i u.1) +
              ENNReal.ofReal α * (ENNReal.ofReal (Fnext D n V i (x + u.1)) +
                ENNReal.ofReal (ε / α)) := by gcongr
          _ = ENNReal.ofReal (D.f n i x + orderCost D n i u.1 +
                α * Fnext D n V i (x + u.1) + ε) := by
              have hFnn := Fnext_nonneg hD n V hV0 i (x + u.1)
              have hc1 : 0 ≤ D.f n i x + orderCost D n i u.1 :=
                add_nonneg (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _) (orderCost_nonneg hD u.2)
              rw [mul_add, ← ENNReal.ofReal_mul hα0.le, ← ENNReal.ofReal_mul hα0.le,
                mul_div_cancel₀ ε hα0.ne',
                ← ENNReal.ofReal_add (mul_nonneg hα0.le hFnn) hε.le,
                ← ENNReal.ofReal_add hc1 (by positivity)]
              congr 1; ring
      have hv_le : vTrunc D α n (k + 1) i x ≤
          ENNReal.ofReal (D.f n i x + orderCost D n i u.1 + α * Fnext D n V i (x + u.1) + ε) :=
        (iInf₂_le (f := fun U (_ : Admissible U) => Jtrunc D α n (k + 1) i x U) U hUadm).trans
          hJ_bound
      have hFnn := Fnext_nonneg hD n V hV0 i (x + u.1)
      have hc1 : 0 ≤ D.f n i x + orderCost D n i u.1 :=
        add_nonneg (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _) (orderCost_nonneg hD u.2)
      calc (vTrunc D α n (k + 1) i x).toReal
          ≤ (ENNReal.ofReal (D.f n i x + orderCost D n i u.1 +
              α * Fnext D n V i (x + u.1) + ε)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hv_le
        _ = D.f n i x + orderCost D n i u.1 + α * Fnext D n V i (x + u.1) + ε :=
            ENNReal.toReal_ofReal (by positivity)
    have hinf := le_ciInf hle_u
    linarith
  · -- Direction `≥`: for any admissible `U`, peel off period 0 via `Jtrunc_succ`.
    set rhs := D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D n i u.1 + α * Fnext D n V i (x + u.1))
    have hge_U : ∀ U : Policy L, Admissible U →
        ENNReal.ofReal rhs ≤ Jtrunc D α n (k + 1) i x U := by
      intro U hU
      rw [Jtrunc_succ hD hα0 n k i x U hU]
      set u0 : {u : ℝ // 0 ≤ u} := ⟨U 0 (fun _ => i) Fin.elim0, hU.1 _ _ _⟩
      have hinf_le : ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u.1 + α * Fnext D n V i (x + u.1)) ≤
          orderCost D n i u0.1 + α * Fnext D n V i (x + u0.1) := ciInf_le hbdd u0
      have hFnn := Fnext_nonneg hD n V hV0 i (x + u0.1)
      have hc1 : 0 ≤ D.f n i x + orderCost D n i u0.1 :=
        add_nonneg (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _) (orderCost_nonneg hD u0.2)
      calc ENNReal.ofReal rhs
          ≤ ENNReal.ofReal (D.f n i x + (orderCost D n i u0.1 + α * Fnext D n V i (x + u0.1))) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal (D.f n i x + orderCost D n i u0.1) +
              ENNReal.ofReal α * ENNReal.ofReal (Fnext D n V i (x + u0.1)) := by
            rw [← add_assoc, ENNReal.ofReal_add hc1 (mul_nonneg hα0.le hFnn),
              ENNReal.ofReal_mul hα0.le]
        _ = ENNReal.ofReal (D.f n i x + orderCost D n i u0.1) +
              ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
                ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u0.1 - z) := by
            rw [hF_ofReal (x + u0.1)]
        _ ≤ _ := by
            gcongr with j _ z
            exact iInf₂_le
              (f := fun W (_ : Admissible W) => Jtrunc D α (n + 1) k j (x + u0.1 - z) W)
              (shiftPolicy U i z) (shiftPolicy_adm hU i z)
    have hge_v : ENNReal.ofReal rhs ≤ vTrunc D α n (k + 1) i x := le_iInf₂ hge_U
    rw [← ENNReal.ofReal_toReal (vTrunc_lt_top hD hα0 hα1 n (k + 1) i x).ne] at hge_v
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hge_v

/-! ### Passing to the limit `k → ∞` to obtain Bellman equation (6.2) -/

private lemma f_le_vTrunc_succ {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    D.f n i x ≤ (vTrunc D α n (k + 1) i x).toReal := by
  rw [vTrunc_dp hD hα0 hα1 n k i x]
  have hinf0 : 0 ≤ ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D n i u.1 +
        α * Fnext D n (fun j y => (vTrunc D α (n + 1) k j y).toReal) i (x + u.1)) := by
    refine le_ciInf fun u => add_nonneg (orderCost_nonneg hD u.2) ?_
    exact mul_nonneg hα0.le (Fnext_nonneg hD n _ (fun _ _ => ENNReal.toReal_nonneg) i _)
  linarith

private lemma vTrunc_toReal_tendsto {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n : ℕ) (i : Fin L) (x : ℝ) :
    Tendsto (fun k => (vTrunc D α n k i x).toReal) atTop (𝓝 (vLim D α n i x).toReal) := by
  have h68 := theorem_6_1_eq_6_8 D α hD hα0 hα1
  have hmono : Monotone (fun k => vTrunc D α n k i x) :=
    monotone_nat_of_le_succ fun k => h68.2.1 n k i x
  have hlim : Tendsto (fun k => vTrunc D α n k i x) atTop (𝓝 (vLim D α n i x)) :=
    tendsto_atTop_iSup hmono
  exact (ENNReal.continuousAt_toReal (vLim_lt_top hD hα0 hα1 n i x).ne).tendsto.comp hlim

private lemma vTrunc_toReal_mono {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n : ℕ) (i : Fin L) (x : ℝ) :
    Monotone (fun k => (vTrunc D α n k i x).toReal) := by
  have h68 := theorem_6_1_eq_6_8 D α hD hα0 hα1
  refine monotone_nat_of_le_succ fun k => ?_
  exact ENNReal.toReal_mono (vTrunc_lt_top hD hα0 hα1 n (k + 1) i x).ne (h68.2.1 n k i x)

private lemma vLim_bellman {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    BellmanInf D α (fun n i x => (vLim D α n i x).toReal) := by
  intro n i x
  set V : ℕ → Fin L → ℝ → ℝ := fun m j y => (vLim D α m j y).toReal
  set Vk : ℕ → ℕ → Fin L → ℝ → ℝ := fun m k j y => (vTrunc D α m k j y).toReal
  have hApos := linConst_pos hD hα0 hα1
  have hVm : ∀ m j, Measurable (V m j) :=
    fun m j => (vLim_toReal_continuous hD hα0 hα1 m j).measurable
  have hVkm : ∀ m k j, Measurable (Vk m k j) :=
    fun m k j => (vTrunc_toReal_continuous hD hα0 hα1 m k j).measurable
  have hV0 : ∀ m j y, 0 ≤ V m j y := fun _ _ _ => ENNReal.toReal_nonneg
  have hVk0 : ∀ m k j y, 0 ≤ Vk m k j y := fun _ _ _ _ => ENNReal.toReal_nonneg
  have hVgr : ∀ m j y, V m j y ≤ linConst D α * (1 + |y|) :=
    fun m j y => vLim_toReal_le_linear hD hα0 hα1 m j y
  have hVkgr : ∀ m k j y, Vk m k j y ≤ linConst D α * (1 + |y|) :=
    fun m k j y => vTrunc_toReal_le_linear hD hα0 hα1 m k j y
  have hVkleV : ∀ m k j y, Vk m k j y ≤ V m j y := fun m k j y =>
    ENNReal.toReal_mono (vLim_lt_top hD hα0 hα1 m j y).ne
      (le_iSup (fun k => vTrunc D α m k j y) k)
  have hbdd : BddBelow (Set.range fun u : {u : ℝ // 0 ≤ u} =>
      orderCost D n i u.1 + α * Fnext D n (V (n + 1)) i (x + u.1)) :=
    dp_bddBelow hD hα0 n (V (n + 1)) (hV0 (n + 1)) i x
  apply le_antisymm
  · -- Direction `≤`: V_n(i, x) ≤ f_n(i, x) + inf_{u ≥ 0} {c_n(i, u) + α F_{n+1}(V_{n+1})(i, x + u)}
    have hle_u : ∀ u : {u : ℝ // 0 ≤ u},
        V n i x - D.f n i x ≤ orderCost D n i u.1 + α * Fnext D n (V (n + 1)) i (x + u.1) := by
      intro u
      have hstep : ∀ k : ℕ, Vk n (k + 1) i x ≤
          D.f n i x + orderCost D n i u.1 + α * Fnext D n (V (n + 1)) i (x + u.1) := by
        intro k
        dsimp only [Vk]
        rw [vTrunc_dp hD hα0 hα1 n k i x]
        have h1 : ⨅ w : {w : ℝ // 0 ≤ w},
              (orderCost D n i w.1 + α * Fnext D n (Vk (n + 1) k) i (x + w.1)) ≤
            orderCost D n i u.1 + α * Fnext D n (Vk (n + 1) k) i (x + u.1) :=
          ciInf_le (dp_bddBelow hD hα0 n (Vk (n + 1) k) (hVk0 (n + 1) k) i x) u
        have h2 : Fnext D n (Vk (n + 1) k) i (x + u.1) ≤ Fnext D n (V (n + 1)) i (x + u.1) :=
          Fnext_mono hD n (Vk (n + 1) k) (V (n + 1)) (linConst D α) hApos.le
            (hVkm (n + 1) k) (hVk0 (n + 1) k) (hVkgr (n + 1) k)
            (hVm (n + 1)) (hV0 (n + 1)) (hVgr (n + 1)) (hVkleV (n + 1) k) i (x + u.1)
        linarith [mul_le_mul_of_nonneg_left h2 hα0.le]
      have hlim : Tendsto (fun k => Vk n (k + 1) i x) atTop (𝓝 (V n i x)) :=
        (vTrunc_toReal_tendsto hD hα0 hα1 n i x).comp (tendsto_add_atTop_nat 1)
      have := le_of_tendsto hlim (Eventually.of_forall hstep)
      linarith
    linarith [le_ciInf hle_u]
  · -- Direction `≥`: coercivity via `Cond42` + compactness on `[0, R]` + monotonicity + DCT.
    set B := V n i x - D.f n i x + 1
    -- Coercivity: α * (c_n(i) * (x + u) + F_{n+1}(f_{n+1})(i, x + u)) - c_n(i) * x → ∞
    have hcoer : Tendsto (fun u : ℝ =>
        α * (D.c n i * (x + u) + Fnext D n (D.f (n + 1)) i (x + u)) - D.c n i * x)
        atTop atTop := by
      have h1 : Tendsto (fun u : ℝ => x + u) atTop atTop :=
        tendsto_atTop_add_const_left atTop x tendsto_id
      have h2 : Tendsto (fun u : ℝ => D.c n i * (x + u) + Fnext D n (D.f (n + 1)) i (x + u))
          atTop atTop := (h42 n i).comp h1
      have h3 : Tendsto (fun u : ℝ =>
          α * (D.c n i * (x + u) + Fnext D n (D.f (n + 1)) i (x + u))) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hα0 h2
      simpa [sub_eq_add_neg] using Filter.Tendsto.atTop_add h3 tendsto_const_nhds
    obtain ⟨R₁, hR₁⟩ := (tendsto_atTop.mp hcoer (B + 1)).exists_forall_of_atTop
    set R := max (max R₁ (-x)) 0
    have hR0 : 0 ≤ R := le_max_right _ _
    -- Uniform coercivity bound for all k ≥ 1 and u > R
    have hgtR : ∀ (k : ℕ) (u : ℝ), R < u →
        B < orderCost D n i u + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u) := by
      intro k u hu
      have huR1 : R₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu.le
      have hxu : 0 ≤ x + u := by
        have : -x ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu.le
        linarith
      have hfm : ∀ j, Measurable (D.f (n + 1) j) :=
        fun j => (continuous_of_convex_univ (hD.2.2.2.2.2.2.2.2.2.1 (n + 1) j)).measurable
      have hf0 : ∀ j y, 0 ≤ D.f (n + 1) j y := hD.2.2.2.2.2.2.2.2.2.2.1 (n + 1)
      have hC_le_A : D.C ≤ linConst D α := by
        have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h1 : 0 < 1 - α := by linarith
        have h2 : D.C ≤ D.C / (1 - α) := by
          rw [le_div_iff₀ h1]; nlinarith
        have h3 : D.C / (1 - α) ≤ linConst D α := by
          unfold linConst
          apply div_le_div_of_nonneg_right _ h1.le
          have : 0 ≤ α * (D.C / (1 - α)) * max D.M 0 := by
            have := le_max_right D.M 0; positivity
          linarith
        exact h2.trans h3
      have hfgr : ∀ j y, D.f (n + 1) j y ≤ linConst D α * (1 + |y|) := fun j y =>
        (hD.2.2.2.2.2.2.2.2.2.2.2.2.2 (n + 1) j y).trans
          (mul_le_mul_of_nonneg_right hC_le_A (by positivity))
      have hFge : Fnext D n (D.f (n + 1)) i (x + u) ≤ Fnext D n (Vk (n + 1) (k + 1)) i (x + u) :=
        Fnext_mono hD n (D.f (n + 1)) (Vk (n + 1) (k + 1)) (linConst D α) hApos.le
          hfm hf0 hfgr (hVkm (n + 1) (k + 1)) (hVk0 (n + 1) (k + 1)) (hVkgr (n + 1) (k + 1))
          (fun j y => f_le_vTrunc_succ hD hα0 hα1 (n + 1) k j y) i (x + u)
      have hKnn : 0 ≤ D.K n i * delta u :=
        mul_nonneg (hD.2.2.2.2.2.2.2.1 n i) (delta_nonneg u)
      have hcnn : 0 ≤ D.c n i := hD.2.2.2.2.2.2.2.2.1 n i
      have hcxu : α * (D.c n i * (x + u)) ≤ D.c n i * (x + u) := by
        nlinarith [mul_nonneg hcnn hxu]
      have hcoer_u := hR₁ u huR1
      have hord : D.c n i * u ≤ orderCost D n i u := by unfold orderCost; linarith
      have : α * (D.c n i * (x + u) + Fnext D n (D.f (n + 1)) i (x + u)) - D.c n i * x ≤
          orderCost D n i u + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u) := by
        nlinarith
      linarith
    -- Pick approximate minimizers u_k ∈ [0, R] for each k : ℕ (at horizon k + 1)
    have hex_u : ∀ k : ℕ, ∃ u : {u : ℝ // 0 ≤ u}, u.1 ≤ R ∧
        orderCost D n i u.1 + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u.1) ≤
          V n i x - D.f n i x + 1 / ((k : ℝ) + 2) := by
      intro k
      set Ik := ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u.1 + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u.1))
      have hIk_le : Ik ≤ V n i x - D.f n i x := by
        have hdp := vTrunc_dp hD hα0 hα1 n (k + 1) i x
        have hle := hVkleV n (k + 2) i x
        linarith
      have hpos_eps : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
      have hlt : Ik < Ik + 1 / ((k : ℝ) + 2) := by linarith
      obtain ⟨u, hu⟩ := exists_lt_of_ciInf_lt hlt
      have hu_bound : orderCost D n i u.1 + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u.1) ≤
          V n i x - D.f n i x + 1 / ((k : ℝ) + 2) := by linarith
      have hu_lt_B : orderCost D n i u.1 + α * Fnext D n (Vk (n + 1) (k + 1)) i (x + u.1) < B := by
        have hfrac : (1 : ℝ) / ((k : ℝ) + 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        dsimp only [B]; linarith
      have huR : u.1 ≤ R := by
        by_contra hgt
        push Not at hgt
        linarith [hgtR k u.1 hgt]
      exact ⟨u, huR, hu_bound⟩
    choose uk hukR huk_le using hex_u
    -- Extract convergent subsequence u_{φ(m)} → u_* ∈ [0, R]
    have hmem : ∀ k, (uk k).1 ∈ Set.Icc (0 : ℝ) R := fun k => ⟨(uk k).2, hukR k⟩
    obtain ⟨ustar, hustar_mem, φ, hφ_mono, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hmem
    -- Show g_{M+1}(u_*) ≤ V_n(i, x) - f_n(i, x) for every M : ℕ
    have hM_bound : ∀ M : ℕ,
        orderCost D n i ustar + α * Fnext D n (Vk (n + 1) (M + 1)) i (x + ustar) ≤
          V n i x - D.f n i x := by
      intro M
      have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hL : 0 ≤ D.C / (1 - α) := div_nonneg hC.le (by linarith)
      have hFcont : Continuous (Fnext D n (Vk (n + 1) (M + 1)) i) := by
        refine continuous_of_lip hL fun y y' => ?_
        refine Fnext_lip hD n (Vk (n + 1) (M + 1)) (linConst D α) (D.C / (1 - α))
          hApos.le (hVkm (n + 1) (M + 1))
          (hVk0 (n + 1) (M + 1)) (hVkgr (n + 1) (M + 1)) ?_ i y y'
        intro j a b
        calc |Vk (n + 1) (M + 1) j b - Vk (n + 1) (M + 1) j a|
            ≤ D.C * |b - a| / (1 - α) :=
              (appendix_lipschitz D α hD hα0 hα1).1 (n + 1) (M + 1) j a b
          _ = D.C / (1 - α) * |b - a| := by ring
      have hF_lim : Tendsto (fun m => Fnext D n (Vk (n + 1) (M + 1)) i (x + (uk (φ m)).1))
          atTop (𝓝 (Fnext D n (Vk (n + 1) (M + 1)) i (x + ustar))) :=
        (hFcont.continuousAt.tendsto).comp (tendsto_const_nhds.add hφ_lim)
      have hrhs_lim : Tendsto (fun m => V n i x - D.f n i x + 1 / ((φ m : ℝ) + 2))
          atTop (𝓝 (V n i x - D.f n i x)) := by
        have h1 : Tendsto (fun m : ℕ => ((φ m : ℝ) + 2)) atTop atTop :=
          Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop)
            tendsto_const_nhds
        have h2 : Tendsto (fun m : ℕ => (1 : ℝ) / ((φ m : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop h1
        simpa using tendsto_const_nhds.add h2
      have hev_le : ∀ᶠ m in atTop,
          orderCost D n i (uk (φ m)).1 +
            α * Fnext D n (Vk (n + 1) (M + 1)) i (x + (uk (φ m)).1) ≤
          V n i x - D.f n i x + 1 / ((φ m : ℝ) + 2) := by
        filter_upwards [eventually_ge_atTop M] with m hm
        have hle_idx : M + 1 ≤ φ m + 1 := Nat.succ_le_succ (hm.trans (hφ_mono.id_le m))
        have hFm : Fnext D n (Vk (n + 1) (M + 1)) i (x + (uk (φ m)).1) ≤
            Fnext D n (Vk (n + 1) (φ m + 1)) i (x + (uk (φ m)).1) :=
          Fnext_mono hD n (Vk (n + 1) (M + 1)) (Vk (n + 1) (φ m + 1)) (linConst D α) hApos.le
            (hVkm (n + 1) (M + 1)) (hVk0 (n + 1) (M + 1)) (hVkgr (n + 1) (M + 1))
            (hVkm (n + 1) (φ m + 1)) (hVk0 (n + 1) (φ m + 1)) (hVkgr (n + 1) (φ m + 1))
            (fun j y => vTrunc_toReal_mono hD hα0 hα1 (n + 1) j y hle_idx) i _
        linarith [huk_le (φ m), mul_le_mul_of_nonneg_left hFm hα0.le]
      rcases eq_or_lt_of_le hustar_mem.1 with hzero | hpos
      · -- Case u_* = 0
        rw [← hzero, orderCost_zero, zero_add]
        have hlhs_lim : Tendsto (fun m =>
            D.c n i * (uk (φ m)).1 + α * Fnext D n (Vk (n + 1) (M + 1)) i (x + (uk (φ m)).1))
            atTop (𝓝 (0 + α * Fnext D n (Vk (n + 1) (M + 1)) i (x + 0))) := by
          have h1 : Tendsto (fun m => D.c n i * (uk (φ m)).1) atTop (𝓝 0) := by
            simpa [← hzero] using tendsto_const_nhds.mul hφ_lim
          have h2 : Tendsto (fun m => α * Fnext D n (Vk (n + 1) (M + 1)) i (x + (uk (φ m)).1))
              atTop (𝓝 (α * Fnext D n (Vk (n + 1) (M + 1)) i (x + 0))) := by
            simpa [← hzero] using tendsto_const_nhds.mul hF_lim
          exact h1.add h2
        rw [zero_add] at hlhs_lim
        refine le_of_tendsto_of_tendsto hlhs_lim hrhs_lim ?_
        filter_upwards [hev_le] with m hm
        have hKnn : 0 ≤ D.K n i * delta (uk (φ m)).1 :=
          mul_nonneg (hD.2.2.2.2.2.2.2.1 n i) (delta_nonneg _)
        have hord : D.c n i * (uk (φ m)).1 ≤ orderCost D n i (uk (φ m)).1 := by
          unfold orderCost; linarith
        linarith
      · -- Case 0 < u_*
        have hev_pos : ∀ᶠ m in atTop, 0 < (uk (φ m)).1 :=
          hφ_lim.eventually (isOpen_Ioi.mem_nhds hpos)
        have hord_lim : Tendsto (fun m => orderCost D n i (uk (φ m)).1)
            atTop (𝓝 (orderCost D n i ustar)) := by
          have hcont_lim : Tendsto (fun m => D.K n i * 1 + D.c n i * (uk (φ m)).1)
              atTop (𝓝 (D.K n i * 1 + D.c n i * ustar)) :=
            tendsto_const_nhds.add (tendsto_const_nhds.mul hφ_lim)
          have heq_u : orderCost D n i ustar = D.K n i * 1 + D.c n i * ustar := by
            unfold orderCost delta; simp [hpos]
          rw [heq_u]
          refine hcont_lim.congr' ?_
          filter_upwards [hev_pos] with m hm
          unfold orderCost delta; simp [hm]
        exact le_of_tendsto_of_tendsto (hord_lim.add (tendsto_const_nhds.mul hF_lim)) hrhs_lim hev_le
    -- Now take M → ∞ using Dominated Convergence (`Fnext_tendsto`)
    have hFM_lim : Tendsto (fun M =>
        orderCost D n i ustar + α * Fnext D n (Vk (n + 1) (M + 1)) i (x + ustar))
        atTop (𝓝 (orderCost D n i ustar + α * Fnext D n (V (n + 1)) i (x + ustar))) := by
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      exact Fnext_tendsto hD n (fun M => Vk (n + 1) (M + 1)) (V (n + 1)) (linConst D α) hApos.le
        (fun M => hVkm (n + 1) (M + 1)) (fun M => hVk0 (n + 1) (M + 1))
        (fun M => hVkgr (n + 1) (M + 1))
        (fun j y => (vTrunc_toReal_tendsto hD hα0 hα1 (n + 1) j y).comp
          (tendsto_add_atTop_nat 1)) i (x + ustar)
    have hustar_le : orderCost D n i ustar + α * Fnext D n (V (n + 1)) i (x + ustar) ≤
        V n i x - D.f n i x :=
      le_of_tendsto hFM_lim (Eventually.of_forall hM_bound)
    have hinf_le : ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u.1 + α * Fnext D n (V (n + 1)) i (x + u.1)) ≤
        orderCost D n i ustar + α * Fnext D n (V (n + 1)) i (x + ustar) :=
      ciInf_le hbdd ⟨ustar, hustar_mem.1⟩
    linarith

end SethiChengSS.Infinite.Eq69

open Filter Topology SethiChengSS.Infinite SethiChengSS.Infinite.Eq69

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h42 : Cond42 D)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n i x, Tendsto (fun k => vTrunc D α n k i x) atTop (𝓝 (vLim D α n i x))) ∧
    (∀ n i x, vLim D α n i x < ⊤) ∧
    BellmanInf D α (fun n i x => (vLim D α n i x).toReal) ∧
    (∀ n, InB1 (fun i x => (vLim D α n i x).toReal)) := by
  have h68 := theorem_6_1_eq_6_8 D α hD hα0 hα1
  refine ⟨fun n i x => ?_, fun n i x => ?_, ?_, fun n => ?_⟩
  · exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun k => h68.2.1 n k i x)
  · exact vLim_lt_top hD hα0 hα1 n i x
  · exact vLim_bellman hD h42 hα0 hα1
  · refine ⟨⟨fun _ _ => ENNReal.toReal_nonneg,
      fun _ i x => (vLim D α n i x).toReal,
      fun _ j => vLim_toReal_continuous hD hα0 hα1 n j,
      fun _ _ _ => ENNReal.toReal_nonneg,
      fun _ _ => tendsto_const_nhds⟩,
      linConst D α, linConst_pos hD hα0 hα1,
      fun i x => vLim_toReal_le_linear hD hα0 hα1 n i x⟩
