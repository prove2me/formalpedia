-- Prove2me | solution 1 for SethiChengSS.Infinite.theorem_6_1_eq_6_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:00:09.529818+00:00
-- url     : https://prove2.me/submissions/e7ce0074-4219-45e3-a423-02cd28d40318

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_8
import Theorems.Thm_SethiChengSS_Infinite_appendix_lipschitz

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.Thm610

open SethiChengSS.Infinite

variable {L : ℕ}

/-! ### Section 1: Standing assumptions, basic bounds, and measurability -/

lemma hP_nonneg {D : Model L} (hD : Standing D) (i j : Fin L) : 0 ≤ D.P i j := hD.1 i j
lemma hP_sum {D : Model L} (hD : Standing D) (i : Fin L) : ∑ j, D.P i j = 1 := hD.2.1 i
lemma hφ_meas {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : Measurable (D.φ k i) :=
  hD.2.2.1 k i
lemma hφ_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) : 0 ≤ D.φ k i z :=
  hD.2.2.2.1 k i z
lemma hφ_neg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) {z : ℝ} (hz : z < 0) :
    D.φ k i z = 0 := hD.2.2.2.2.1 k i z hz
lemma hφ_int {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫⁻ z, ENNReal.ofReal (D.φ k i z) = 1 := hD.2.2.2.2.2.1 k i
lemma hφ_mean {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫⁻ z, ENNReal.ofReal (z * D.φ k i z) ≤ ENNReal.ofReal D.M := hD.2.2.2.2.2.2.1 k i
lemma hK_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : 0 ≤ D.K k i :=
  hD.2.2.2.2.2.2.2.1 k i
lemma hc_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : 0 ≤ D.c k i :=
  hD.2.2.2.2.2.2.2.2.1 k i
lemma hf_conv {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ConvexOn ℝ Set.univ (D.f k i) := hD.2.2.2.2.2.2.2.2.2.1 k i
lemma hf_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (x : ℝ) : 0 ≤ D.f k i x :=
  hD.2.2.2.2.2.2.2.2.2.2.1 k i x
lemma hf_zero {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : D.f k i 0 = 0 :=
  hD.2.2.2.2.2.2.2.2.2.2.2.1 k i
lemma hC_pos {D : Model L} (hD : Standing D) : 0 < D.C :=
  hD.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma hf_growth {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (x : ℝ) :
    D.f k i x ≤ D.C * (1 + |x|) := hD.2.2.2.2.2.2.2.2.2.2.2.2.2 k i x

lemma continuous_of_convex_univ {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) : Continuous g := by
  have := hg.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma hf_cont {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : Continuous (D.f k i) :=
  continuous_of_convex_univ (hf_conv hD k i)

lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

lemma delta_zero : delta 0 = 0 := by
  unfold delta; simp

lemma delta_pos {z : ℝ} (hz : 0 < z) : delta z = 1 := by
  unfold delta; simp [hz]

lemma orderCost_zero (D : Model L) (k : ℕ) (i : Fin L) : orderCost D k i 0 = 0 := by
  unfold orderCost; simp [delta_zero]

lemma orderCost_nonneg {D : Model L} (hD : Standing D) {k : ℕ} {i : Fin L} {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ orderCost D k i u :=
  add_nonneg (mul_nonneg (hK_nonneg hD k i) (delta_nonneg u))
    (mul_nonneg (hc_nonneg hD k i) hu)

lemma pathWeight_nonneg {D : Model L} (hD : Standing D) (n : ℕ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : 0 ≤ pathWeight D n σ ξ :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (hP_nonneg hD _ _) (hφ_nonneg hD _ _ _)

lemma truncCost_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n : ℕ)
    (U : Policy L) (hU : ∀ t σ ξ, 0 ≤ U t σ ξ) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : 0 ≤ truncCost D α n U x σ ξ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hα _)
    (add_nonneg (orderCost_nonneg hD (hU _ _ _)) (hf_nonneg hD _ _ _))

lemma meas_init {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.init ξ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

lemma meas_tail {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.tail ξ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

lemma meas_cons_pair {m : ℕ} :
    Measurable (fun p : ℝ × (Fin m → ℝ) => (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun a => ?_
  refine Fin.cases ?_ ?_ a
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · intro b
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply b).comp measurable_snd

lemma meas_dmHist {m : ℕ} (t : Fin m) : Measurable (fun ξ : Fin m → ℝ => dmHist ξ t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

lemma meas_surplus (U : Policy L) (x : ℝ) (hU : ∀ t σ, Measurable (U t σ)) :
    ∀ t, ∀ σ : Fin (t + 1) → Fin L, Measurable (surplus U x t σ) := by
  intro t
  induction t with
  | zero => intro _; exact measurable_const
  | succ t ih =>
    intro σ
    exact (((ih _).comp meas_init).add ((hU t _).comp meas_init)).sub (measurable_pi_apply _)

lemma meas_delta : Measurable delta := by
  unfold delta
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

lemma meas_orderCost (D : Model L) (k : ℕ) (i : Fin L) : Measurable (orderCost D k i) := by
  unfold orderCost
  exact (measurable_const.mul meas_delta).add (measurable_const.mul measurable_id)

lemma meas_truncCost {D : Model L} (hD : Standing D) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ)
    (hU : ∀ t σ, Measurable (U t σ)) {k : ℕ} (σ : Fin (k + 1) → Fin L) :
    Measurable (fun ξ => truncCost D α n U x σ ξ) := by
  unfold truncCost
  refine Finset.measurable_sum _ fun t _ => ?_
  exact measurable_const.mul (((meas_orderCost D _ _).comp ((hU _ _).comp (meas_dmHist t))).add
    ((hf_cont hD _ _).measurable.comp ((meas_surplus U x hU _ _).comp (meas_dmHist t))))

lemma meas_pathWeight {D : Model L} (hD : Standing D) (n : ℕ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) : Measurable (fun ξ : Fin k → ℝ => pathWeight D n σ ξ) := by
  unfold pathWeight
  exact Finset.measurable_prod _ fun t _ =>
    measurable_const.mul ((hφ_meas hD _ _).comp (measurable_pi_apply _))

lemma Jtrunc_zero (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    Jtrunc D α n 0 i x U = 0 := by
  unfold Jtrunc truncCost; simp

lemma zero_adm : Admissible (zeroPolicy : Policy L) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ => measurable_const⟩

/-! ### Section 2: `Fin.cons` decomposition (`Jtrunc_cons`), `weight_sum`, and `Jtrunc_shift` -/

def shiftPolicy (U : Policy L) (i : Fin L) (z : ℝ) : Policy L :=
  fun t σ ξ => U (t + 1) (Fin.cons i σ) (Fin.cons z ξ)

lemma shiftPolicy_adm {U : Policy L} (hU : Admissible U) (i : Fin L) (z : ℝ) :
    Admissible (shiftPolicy U i z) := by
  refine ⟨fun t σ ξ => hU.1 (t + 1) (Fin.cons i σ) (Fin.cons z ξ), fun t σ => ?_⟩
  exact (hU.2 (t + 1) (Fin.cons i σ)).comp (meas_cons_pair.comp (measurable_const.prodMk measurable_id))

lemma shiftPolicy_zero (i : Fin L) (z : ℝ) :
    shiftPolicy (zeroPolicy : Policy L) i z = zeroPolicy := rfl

lemma stHist_cons_zero {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L) :
    stHist (Fin.cons i σ' : Fin (k + 2) → Fin L) (0 : Fin (k + 1)) = fun _ => i := by
  funext a
  have ha0 : a.val = 0 := by have := a.2; simp at this; omega
  have hcast : Fin.castLE (Nat.succ_le_succ (0 : Fin (k + 1)).isLt.le) a = (0 : Fin (k + 2)) :=
    Fin.ext ha0
  simp only [stHist]
  rw [hcast]
  simp

lemma dmHist_cons_zero {k : ℕ} (z : ℝ) (ξ' : Fin k → ℝ) :
    dmHist (Fin.cons z ξ' : Fin (k + 1) → ℝ) (0 : Fin (k + 1)) = Fin.elim0 := by
  funext a; exact Fin.elim0 a

lemma stHist_cons_succ {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L) (t : Fin k) :
    stHist (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ = Fin.cons i (stHist σ' t) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [stHist]
  · intro b
    simp [stHist]

lemma dmHist_cons_succ {k : ℕ} (z : ℝ) (ξ' : Fin k → ℝ) (t : Fin k) :
    dmHist (Fin.cons z ξ' : Fin (k + 1) → ℝ) t.succ = Fin.cons z (dmHist ξ' t) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [dmHist]
  · intro b
    simp [dmHist]

lemma init_cons {β : Type*} {t : ℕ} (a : β) (f : Fin (t + 1) → β) :
    Fin.init (Fin.cons a f : Fin (t + 2) → β) = Fin.cons a (Fin.init f) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.init]
  · intro b
    simp [Fin.init]

lemma init_cons_zero {β : Type*} (a : β) (f : Fin 1 → β) :
    Fin.init (Fin.cons a f : Fin 2 → β) = fun _ => a := by
  funext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  simp [Fin.init]

lemma init_cons_empty {β : Type*} (a : β) (f : Fin 0 → β) :
    Fin.init (Fin.cons a f : Fin 1 → β) = Fin.elim0 := by
  funext j; exact Fin.elim0 j

lemma surplus_cons_succ (U : Policy L) (x : ℝ) (i : Fin L) (z : ℝ) :
    ∀ (t : ℕ) (σ' : Fin (t + 1) → Fin L) (ξ' : Fin t → ℝ),
      surplus U x (t + 1) (Fin.cons i σ') (Fin.cons z ξ') =
        surplus (shiftPolicy U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t σ' ξ' := by
  intro t
  induction t with
  | zero =>
    intro σ' ξ'
    simp only [surplus, init_cons_zero, init_cons_empty]
    have hl : (Fin.cons z ξ' : Fin 1 → ℝ) (Fin.last 0) = z := by
      change (Fin.cons z ξ' : Fin 1 → ℝ) 0 = z
      simp
    rw [hl]
  | succ t ih =>
    intro σ' ξ'
    change surplus U x (t + 1) (Fin.init (Fin.cons i σ' : Fin (t + 3) → Fin L))
          (Fin.init (Fin.cons z ξ' : Fin (t + 2) → ℝ)) +
        U (t + 1) (Fin.init (Fin.cons i σ' : Fin (t + 3) → Fin L))
          (Fin.init (Fin.cons z ξ' : Fin (t + 2) → ℝ)) -
        (Fin.cons z ξ' : Fin (t + 2) → ℝ) (Fin.last (t + 1)) =
      surplus (shiftPolicy U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t (Fin.init σ') (Fin.init ξ') +
        shiftPolicy U i z t (Fin.init σ') (Fin.init ξ') - ξ' (Fin.last t)
    rw [init_cons, init_cons]
    have hl : (Fin.cons z ξ' : Fin (t + 2) → ℝ) (Fin.last (t + 1)) = ξ' (Fin.last t) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [hl, ih]
    rfl

lemma pathWeight_cons (D : Model L) (n : ℕ) {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L)
    (z : ℝ) (ξ' : Fin k → ℝ) :
    pathWeight D n (Fin.cons i σ' : Fin (k + 2) → Fin L) (Fin.cons z ξ' : Fin (k + 1) → ℝ) =
      (D.P i (σ' 0) * D.φ n i z) * pathWeight D (n + 1) σ' ξ' := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  have h1 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.castSucc = σ' t.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have h2 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.succ = σ' t.succ := by
    rw [Fin.cons_succ]
  have h3 : (Fin.cons z ξ' : Fin (k + 1) → ℝ) t.succ = ξ' t := Fin.cons_succ ..
  have h4 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
  rw [h1, h2, h3, h4]

lemma truncCost_cons (D : Model L) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ) {k : ℕ}
    (i : Fin L) (σ' : Fin (k + 1) → Fin L) (z : ℝ) (ξ' : Fin k → ℝ) :
    truncCost D α n U x (Fin.cons i σ' : Fin (k + 2) → Fin L) (Fin.cons z ξ' : Fin (k + 1) → ℝ) =
      (orderCost D n i (U 0 (fun _ => i) Fin.elim0) + D.f n i x) +
        α * truncCost D α (n + 1) (shiftPolicy U i z)
              (x + U 0 (fun _ => i) Fin.elim0 - z) σ' ξ' := by
  unfold truncCost
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp [stHist_cons_zero, dmHist_cons_zero, surplus]
  · refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.castSucc = σ' t.castSucc := by
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    have h4 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
    have hpow : α ^ (t.succ : ℕ) = α * α ^ (t : ℕ) := by
      simp [pow_succ, mul_comm]
    rw [h1, stHist_cons_succ, dmHist_cons_succ, h4, hpow, mul_assoc]
    simp only [Fin.val_succ]
    congr 2
    rw [surplus_cons_succ]
    rfl

lemma sum_cons {k : ℕ} (i : Fin L) (F : (Fin (k + 2) → Fin L) → ℝ≥0∞) :
    (∑ σ : Fin (k + 2) → Fin L, if σ 0 = i then F σ else 0) =
      ∑ σ' : Fin (k + 1) → Fin L, F (Fin.cons i σ') := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin L)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [Fin.consEquiv]
  · intro j _ hji
    refine Finset.sum_eq_zero fun σ' _ => ?_
    simp [Fin.consEquiv, hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma cons_symm_eq (k : ℕ) (p : ℝ × (Fin k → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p =
      (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

lemma lintegral_cons (k : ℕ) (G : (Fin (k + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ξ : Fin (k + 1) → ℝ, G ξ ∂(Measure.pi fun _ => volume) =
      ∫⁻ z : ℝ, ∫⁻ ξ' : Fin k → ℝ, G (Fin.cons z ξ' : Fin (k + 1) → ℝ)
        ∂(Measure.pi fun _ => volume) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hvol1 : (Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℝ)) = volume := rfl
  have hvol0 : (Measure.pi fun _ : Fin k => (volume : Measure ℝ)) = volume := rfl
  rw [hvol1]
  have h1 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℝ))) =
      ∫⁻ ξ, G ξ := (MeasurePreserving.symm _ hmp).lintegral_comp hG
  have h2 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℝ))) =
      ∫⁻ z : ℝ, ∫⁻ ξ' : Fin k → ℝ,
        G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm (z, ξ'))
        ∂(Measure.pi fun _ : Fin k => (volume : Measure ℝ)) ∂(volume : Measure ℝ) :=
    lintegral_prod _ (hG.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [← h1, h2]
  simp only [cons_symm_eq]

lemma sum_by_head {k : ℕ} (F : (Fin (k + 1) → Fin L) → ℝ≥0∞) :
    ∑ σ' : Fin (k + 1) → Fin L, F σ' =
      ∑ j : Fin L, ∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then F σ' else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  rw [Finset.sum_eq_single (σ' 0)]
  · simp
  · intro j _ hj; simp [hj.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Total weight of all paths of length `k` started at `i` is `1`. -/
lemma weight_sum {D : Model L} (hD : Standing D) : ∀ (k n : ℕ) (i : Fin L),
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
      intro h; apply hσ
      funext a; have ha : a = 0 := Fin.ext (by omega); subst ha; exact h
  | succ k ih =>
    intro n i
    rw [sum_cons]
    have hstep : ∀ σ' : Fin (k + 1) → Fin L,
        ∫⁻ ξ : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ)
          ∂(Measure.pi fun _ => volume) =
        ENNReal.ofReal (D.P i (σ' 0)) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
            ∂(Measure.pi fun _ => volume) := by
      intro σ'
      have hm : Measurable (fun ξ : Fin (k + 1) → ℝ =>
          ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ)) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)
      rw [lintegral_cons k _ hm]
      have e : ∀ z ξ', ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) =
          (ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
            ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') := by
        intro z ξ'
        rw [pathWeight_cons, ENNReal.ofReal_mul (mul_nonneg (hP_nonneg hD _ _) (hφ_nonneg hD _ _ _)),
          ENNReal.ofReal_mul (hP_nonneg hD _ _)]
      simp only [e]
      have hmw : Measurable (fun ξ' : Fin k → ℝ =>
          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')
      have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
      simp_rw [lintegral_const_mul _ hmw, mul_assoc]
      rw [lintegral_const_mul _ (hmφ.mul_const _), lintegral_mul_const _ hmφ, hφ_int hD n i, one_mul]
    simp_rw [hstep]
    rw [sum_by_head]
    have hinner : ∀ j : Fin L,
        (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal (D.P i j) := by
      intro j
      calc _ = ∑ σ' : Fin (k + 1) → Fin L, ENNReal.ofReal (D.P i j) *
            (if σ' 0 = j then ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) := by
            refine Finset.sum_congr rfl fun σ' _ => ?_
            split_ifs with h <;> simp [h]
        _ = ENNReal.ofReal (D.P i j) * _ := (Finset.mul_sum ..).symm
        _ = ENNReal.ofReal (D.P i j) := by rw [ih (n + 1) j, mul_one]
    simp_rw [hinner]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP_nonneg hD i j), hP_sum hD i,
      ENNReal.ofReal_one]

/-- One-step decomposition of `Jtrunc` by peeling off period `0` (`Fin.cons`). -/
theorem Jtrunc_cons {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 ≤ α)
    (n k : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) (hU : Admissible U) :
    Jtrunc D α n (k + 1) i x U =
      ENNReal.ofReal (orderCost D n i (U 0 (fun _ => i) Fin.elim0) + D.f n i x) +
      ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          Jtrunc D α (n + 1) k j (x + U 0 (fun _ => i) Fin.elim0 - z) (shiftPolicy U i z) := by
  set u₀ := U 0 (fun _ => i) Fin.elim0
  set c₀ := orderCost D n i u₀ + D.f n i x
  have hc₀ : 0 ≤ c₀ := add_nonneg (orderCost_nonneg hD (hU.1 0 _ _)) (hf_nonneg hD n i x)
  unfold Jtrunc
  rw [sum_cons]
  have hterm : ∀ σ' : Fin (k + 1) → Fin L,
      ∫⁻ ξ : Fin (k + 1) → ℝ,
        ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') ξ)
        ∂(Measure.pi fun _ => volume) =
      ENNReal.ofReal c₀ * (ENNReal.ofReal (D.P i (σ' 0)) *
        ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
          ∂(Measure.pi fun _ => volume)) +
      ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
            ∂(Measure.pi fun _ => volume) := by
    intro σ'
    have hmG : Measurable (fun ξ : Fin (k + 1) → ℝ =>
        ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') ξ)) :=
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)).mul
        (ENNReal.measurable_ofReal.comp (meas_truncCost hD α n U x hU.2 _))
    rw [lintegral_cons k _ hmG]
    have hsplit : ∀ z ξ',
        ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') (Fin.cons z ξ')) =
        (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') +
        (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
          (ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')) := by
      intro z ξ'
      have hP := hP_nonneg hD i (σ' 0)
      have hφ := hφ_nonneg hD n i z
      have htc : 0 ≤ truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ' :=
        truncCost_nonneg hD hα0 (n + 1) (shiftPolicy U i z) (shiftPolicy_adm hU i z).1 _ σ' ξ'
      rw [pathWeight_cons, truncCost_cons]
      rw [ENNReal.ofReal_mul (mul_nonneg hP hφ), ENNReal.ofReal_mul hP,
        ENNReal.ofReal_add hc₀ (mul_nonneg hα0 htc), ENNReal.ofReal_mul hα0]
      ring
    simp_rw [hsplit]
    have hm1_inner : ∀ z, Measurable (fun ξ' : Fin k → ℝ =>
        (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) := fun z =>
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')).const_mul _
    have hm2_inner : ∀ z, Measurable (fun ξ' : Fin k → ℝ =>
        ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
          ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')) := fun z =>
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')).mul
        (ENNReal.measurable_ofReal.comp
          (meas_truncCost hD α (n + 1) (shiftPolicy U i z) (x + u₀ - z) (shiftPolicy_adm hU i z).2 σ'))
    have hinner : ∀ z,
        ∫⁻ ξ' : Fin k → ℝ,
          ((ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
            ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') +
          (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
            (ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')))
          ∂(Measure.pi fun _ => volume) =
        (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
            ∂(Measure.pi fun _ => volume)) * ENNReal.ofReal (D.φ n i z) +
        (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0))) *
          (ENNReal.ofReal (D.φ n i z) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
              ∂(Measure.pi fun _ => volume)) := by
      intro z
      have hmpw : Measurable (fun ξ' : Fin k → ℝ =>
          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')
      rw [lintegral_add_left (hm1_inner z),
        lintegral_const_mul _ hmpw,
        lintegral_const_mul _ (hm2_inner z)]
      ring
    simp_rw [hinner]
    have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
      ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
    -- Joint measurability of the second inner integrand in `(z, ξ')`:
    have hm_joint : Measurable (fun p : ℝ × (Fin k → ℝ) =>
        ENNReal.ofReal (pathWeight D (n + 1) σ' p.2) *
          ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2)) := by
      have hm_pw : Measurable (fun p : ℝ × (Fin k → ℝ) =>
          ENNReal.ofReal (pathWeight D (n + 1) σ' p.2)) :=
        (ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')).comp measurable_snd
      have hm_tc : Measurable (fun p : ℝ × (Fin k → ℝ) =>
          truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2) := by
        unfold truncCost
        refine Finset.measurable_sum _ fun t _ => ?_
        have hst : ∀ p : ℝ × (Fin k → ℝ),
            (shiftPolicy U i p.1) t (stHist σ' t) (dmHist p.2 t) =
              U (t + 1) (Fin.cons i (stHist σ' t)) (dmHist (Fin.cons p.1 p.2) t.succ) := by
          intro p; rw [dmHist_cons_succ]; rfl
        have hsu : ∀ p : ℝ × (Fin k → ℝ),
            surplus (shiftPolicy U i p.1) (x + u₀ - p.1) t (stHist σ' t) (dmHist p.2 t) =
              surplus U x (t + 1) (Fin.cons i (stHist σ' t)) (dmHist (Fin.cons p.1 p.2) t.succ) := by
          intro p; rw [dmHist_cons_succ, surplus_cons_succ]
        simp_rw [hst, hsu]
        refine measurable_const.mul (Measurable.add ?_ ?_)
        · exact (meas_orderCost D _ _).comp
            ((hU.2 _ _).comp ((meas_dmHist t.succ).comp meas_cons_pair))
        · exact (hf_cont hD _ _).measurable.comp
            ((meas_surplus U x hU.2 _ _).comp ((meas_dmHist t.succ).comp meas_cons_pair))
      exact hm_pw.mul (ENNReal.measurable_ofReal.comp hm_tc)
    have hm_outer2 : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z) *
        ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
          ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
          ∂(Measure.pi fun _ => volume)) :=
      hmφ.mul hm_joint.lintegral_prod_right'
    rw [lintegral_add_left (hmφ.const_mul _),
      lintegral_const_mul _ hmφ, hφ_int hD n i, mul_one,
      lintegral_const_mul _ hm_outer2]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- Term 1 equals `ENNReal.ofReal c₀`
    rw [← Finset.mul_sum, sum_by_head]
    have h1 : ∀ j : Fin L,
        (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal (D.P i j) := by
      intro j
      calc _ = ∑ σ' : Fin (k + 1) → Fin L, ENNReal.ofReal (D.P i j) *
            (if σ' 0 = j then ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) := by
            refine Finset.sum_congr rfl fun σ' _ => by split_ifs with h <;> simp [h]
        _ = ENNReal.ofReal (D.P i j) * _ := (Finset.mul_sum ..).symm
        _ = ENNReal.ofReal (D.P i j) := by rw [weight_sum hD k (n + 1) j, mul_one]
    simp_rw [h1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP_nonneg hD i j), hP_sum hD i,
      ENNReal.ofReal_one, mul_one]
  · -- Term 2: swap sum over `σ'` and `∫⁻ z`
    rw [sum_by_head, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm_sigma : ∀ σ' : Fin (k + 1) → Fin L,
        Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z) *
          if σ' 0 = j then
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
              ∂(Measure.pi fun _ => volume)
          else 0) := by
      intro σ'
      split_ifs with hσ'
      · have hm_joint : Measurable (fun p : ℝ × (Fin k → ℝ) =>
            ENNReal.ofReal (pathWeight D (n + 1) σ' p.2) *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2)) := by
          have hm_pw : Measurable (fun p : ℝ × (Fin k → ℝ) =>
              ENNReal.ofReal (pathWeight D (n + 1) σ' p.2)) :=
            (ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')).comp measurable_snd
          have hm_tc : Measurable (fun p : ℝ × (Fin k → ℝ) =>
              truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2) := by
            unfold truncCost
            refine Finset.measurable_sum _ fun t _ => ?_
            have hst : ∀ p : ℝ × (Fin k → ℝ),
                (shiftPolicy U i p.1) t (stHist σ' t) (dmHist p.2 t) =
                  U (t + 1) (Fin.cons i (stHist σ' t)) (dmHist (Fin.cons p.1 p.2) t.succ) := by
              intro p; rw [dmHist_cons_succ]; rfl
            have hsu : ∀ p : ℝ × (Fin k → ℝ),
                surplus (shiftPolicy U i p.1) (x + u₀ - p.1) t (stHist σ' t) (dmHist p.2 t) =
                  surplus U x (t + 1) (Fin.cons i (stHist σ' t)) (dmHist (Fin.cons p.1 p.2) t.succ) := by
              intro p; rw [dmHist_cons_succ, surplus_cons_succ]
            simp_rw [hst, hsu]
            refine measurable_const.mul (Measurable.add ?_ ?_)
            · exact (meas_orderCost D _ _).comp
                ((hU.2 _ _).comp ((meas_dmHist t.succ).comp meas_cons_pair))
            · exact (hf_cont hD _ _).measurable.comp
                ((meas_surplus U x hU.2 _ _).comp ((meas_dmHist t.succ).comp meas_cons_pair))
          exact hm_pw.mul (ENNReal.measurable_ofReal.comp hm_tc)
        exact (ENNReal.measurable_ofReal.comp (hφ_meas hD n i)).mul hm_joint.lintegral_prod_right'
      · simp [measurable_const]
    have hrewrite :
        (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
                ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal α * ENNReal.ofReal (D.P i j) *
          ∑ σ' : Fin (k + 1) → Fin L, ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
            if σ' 0 = j then
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
                ∂(Measure.pi fun _ => volume)
            else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ' _ => ?_
      split_ifs with hσ' <;> simp [hσ']
    rw [hrewrite, ← lintegral_finsetSum _ (fun σ' _ => hm_sigma σ'), mul_assoc]
    congr 2
    refine lintegral_congr fun z => ?_
    rw [← Finset.mul_sum]

lemma surplus_congr_start {W₁ W₂ : Policy L} (j : Fin L) (y : ℝ)
    (hW : ∀ t (σ : Fin (t + 1) → Fin L) ξ, σ 0 = j → W₁ t σ ξ = W₂ t σ ξ) :
    ∀ t (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ), σ 0 = j →
      surplus W₁ y t σ ξ = surplus W₂ y t σ ξ := by
  intro t
  induction t with
  | zero => intro _ _ _; rfl
  | succ t ih =>
    intro σ ξ hσ
    have hinit : Fin.init σ 0 = j := by simpa [Fin.init] using hσ
    simp only [surplus, ih (Fin.init σ) (Fin.init ξ) hinit, hW t (Fin.init σ) (Fin.init ξ) hinit]

lemma Jtrunc_congr_start (D : Model L) (α : ℝ) (n k : ℕ) (j : Fin L) (y : ℝ)
    {W₁ W₂ : Policy L}
    (hW : ∀ t (σ : Fin (t + 1) → Fin L) ξ, σ 0 = j → W₁ t σ ξ = W₂ t σ ξ) :
    Jtrunc D α n k j y W₁ = Jtrunc D α n k j y W₂ := by
  unfold Jtrunc
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with hσ
  · refine lintegral_congr fun ξ => ?_
    congr 2
    unfold truncCost
    refine Finset.sum_congr rfl fun t _ => ?_
    have hst : stHist σ t 0 = j := by simpa [stHist] using hσ
    rw [hW t (stHist σ t) (dmHist ξ t) hst, surplus_congr_start j y hW t (stHist σ t) (dmHist ξ t) hst]
  · rfl

lemma surplus_shift (U : Policy L) (x x' : ℝ) :
    ∀ t (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ),
      surplus U x' t σ ξ = surplus U x t σ ξ + (x' - x) := by
  intro t
  induction t with
  | zero => intro _ _; simp only [surplus]; ring
  | succ t ih => intro _ _; simp only [surplus, ih]; ring

lemma f_lipschitz {D : Model L} (hD : Standing D) (k : ℕ) (j : Fin L) (a b : ℝ) :
    D.f k j b - D.f k j a ≤ D.C * |b - a| := by
  have hconv := hf_conv hD k j
  have hnn := hf_nonneg hD k j
  have hgr := hf_growth hD k j
  have hC := hC_pos hD
  rcases lt_trichotomy a b with hab | hab | hab
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (b - a) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := a) (y := b) (z := b + t) trivial trivial hab (by linarith)
      have e1 : b + t - b = t := by ring
      rw [e1] at hs
      have h1 : D.f k j b - D.f k j a ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := by
        rw [div_le_iff₀ (by linarith)] at hs; rw [mul_comm]; exact hs
      have h2 : (D.f k j (b + t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b + t); have := hnn b
        have : |b + t| ≤ |b| + t := (abs_add_le b t).trans_eq (by rw [abs_of_pos ht])
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hlim : Tendsto (fun t : ℝ => (b - a) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((b - a) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hkey)
    rw [abs_of_pos (by linarith : 0 < b - a)]; linarith
  · subst hab; simp
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (a - b) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := b - t) (y := b) (z := a) trivial trivial (by linarith) hab
      have e1 : b - (b - t) = t := by ring
      rw [e1] at hs
      have h1 : D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := by
        have h3 : (D.f k j b - D.f k j (b - t)) / t * (a - b) ≤ D.f k j a - D.f k j b := by
          have := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ a - b)
          rwa [div_mul_cancel₀ _ (by linarith : a - b ≠ 0)] at this
        have e : (a - b) * ((D.f k j (b - t) - D.f k j b) / t) =
            -((D.f k j b - D.f k j (b - t)) / t * (a - b)) := by ring
        rw [e]; linarith
      have h2 : (D.f k j (b - t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b - t); have := hnn b
        have : |b - t| ≤ |b| + t := (abs_sub b t).trans_eq (by rw [abs_of_pos ht])
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hlim : Tendsto (fun t : ℝ => (a - b) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((a - b) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hkey)
    rw [abs_of_neg (by linarith : b - a < 0)]; linarith

lemma geom_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∑ t : Fin k, α ^ (t : ℕ) ≤ 1 / (1 - α) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => α ^ t), geom_sum_eq hα1.ne]
  have e : (α ^ k - 1) / (α - 1) = (1 - α ^ k) / (1 - α) := by
    have : α - 1 ≠ 0 := by linarith
    have : 1 - α ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by have := pow_nonneg hα0.le k; linarith) (by linarith)

lemma truncCost_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (U : Policy L) (x x' : ℝ) {k : ℕ} (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) :
    truncCost D α n U x' σ ξ ≤ truncCost D α n U x σ ξ + D.C * |x' - x| / (1 - α) := by
  have hC := hC_pos hD
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
    rw [add_sub_cancel_left] at this
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

lemma Jtrunc_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
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

/-! ### Section 3: Uniform growth bound for `w`, `vTrunc`, `vLim`, and `InC1` (Part 1) -/

noncomputable def growthA (D : Model L) (α : ℝ) : ℝ := D.C / (1 - α)
noncomputable def growthB (D : Model L) (α : ℝ) : ℝ := D.C * max D.M 0 * α / (1 - α) ^ 2
noncomputable def growthC (D : Model L) (α : ℝ) : ℝ := growthA D α + growthB D α

lemma growthA_pos {D : Model L} (hD : Standing D) {α : ℝ} (hα1 : α < 1) : 0 < growthA D α :=
  div_pos (hC_pos hD) (by linarith)

lemma growthB_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ growthB D α := by
  unfold growthB
  have := hC_pos hD
  have : 0 ≤ max D.M 0 := le_max_right _ _
  have : 0 < 1 - α := by linarith
  positivity

lemma growthC_pos {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < growthC D α := add_pos_of_pos_of_nonneg (growthA_pos hD hα1) (growthB_nonneg hD hα0 hα1)

lemma Jtrunc_zeroPolicy_le {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ k n i x, Jtrunc D α n k i x zeroPolicy ≤
      ENNReal.ofReal (growthA D α * (1 + |x|) + growthB D α) := by
  set A := growthA D α
  set B := growthB D α
  set Mp := max D.M 0
  have hA : 0 < A := growthA_pos hD hα1
  have hB : 0 ≤ B := growthB_nonneg hD hα0 hα1
  have hMp : 0 ≤ Mp := le_max_right _ _
  intro k
  induction k with
  | zero =>
    intro n i x
    rw [Jtrunc_zero]; exact bot_le
  | succ k ih =>
    intro n i x
    rw [Jtrunc_cons hD hα0.le n k i x zeroPolicy zero_adm]
    simp only [zeroPolicy, orderCost_zero, zero_add, add_zero, shiftPolicy_zero]
    have hstep : ∀ j : Fin L,
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy ≤
          ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) := by
      intro j
      have hpoint : ∀ z : ℝ,
          ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy ≤
            ENNReal.ofReal (A * (1 + |x|) + B) * ENNReal.ofReal (D.φ n i z) +
              ENNReal.ofReal A * ENNReal.ofReal (z * D.φ n i z) := by
        intro z
        by_cases hz : z < 0
        · simp [hφ_neg hD n i hz]
        · push Not at hz
          have habs : |x - z| ≤ |x| + z := by
            calc |x - z| ≤ |x| + |z| := abs_sub x z
              _ = |x| + z := by rw [abs_of_nonneg hz]
          have h1 : A * (1 + |x - z|) + B ≤ (A * (1 + |x|) + B) + A * z := by nlinarith
          have hnn1 : 0 ≤ A * (1 + |x|) + B := by positivity
          have hnn2 : 0 ≤ A * z := mul_nonneg hA.le hz
          calc ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
              ≤ ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (A * (1 + |x - z|) + B) := by
                gcongr; exact ih (n + 1) j (x - z)
            _ ≤ ENNReal.ofReal (D.φ n i z) * (ENNReal.ofReal (A * (1 + |x|) + B) + ENNReal.ofReal (A * z)) := by
                gcongr
                exact (ENNReal.ofReal_le_ofReal h1).trans (ENNReal.ofReal_add_le)
            _ = ENNReal.ofReal (A * (1 + |x|) + B) * ENNReal.ofReal (D.φ n i z) +
                  ENNReal.ofReal A * ENNReal.ofReal (z * D.φ n i z) := by
                rw [mul_add, mul_comm (ENNReal.ofReal (D.φ n i z)),
                  ENNReal.ofReal_mul hA.le, ENNReal.ofReal_mul hz]
                ring
      have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
      have hm1 : Measurable (fun z : ℝ => ENNReal.ofReal (A * (1 + |x|) + B) * ENNReal.ofReal (D.φ n i z)) :=
        hmφ.const_mul _
      have hm2 : Measurable (fun z : ℝ => ENNReal.ofReal (z * D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (measurable_id.mul (hφ_meas hD n i))
      calc ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
          ≤ ∫⁻ z : ℝ, (ENNReal.ofReal (A * (1 + |x|) + B) * ENNReal.ofReal (D.φ n i z) +
              ENNReal.ofReal A * ENNReal.ofReal (z * D.φ n i z)) := lintegral_mono hpoint
        _ = ENNReal.ofReal (A * (1 + |x|) + B) * (∫⁻ z, ENNReal.ofReal (D.φ n i z)) +
              ENNReal.ofReal A * (∫⁻ z, ENNReal.ofReal (z * D.φ n i z)) := by
            rw [lintegral_add_left hm1, lintegral_const_mul _ hmφ, lintegral_const_mul _ hm2]
        _ ≤ ENNReal.ofReal (A * (1 + |x|) + B) * 1 + ENNReal.ofReal A * ENNReal.ofReal Mp := by
            rw [hφ_int hD n i]
            gcongr
            exact (hφ_mean hD n i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        _ = ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) := by
            rw [mul_one, ← ENNReal.ofReal_mul hA.le,
              ← ENNReal.ofReal_add (by positivity) (mul_nonneg hA.le hMp)]
    have hsum : ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy ≤
        ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) := by
      calc _ ≤ ∑ j : Fin L, ENNReal.ofReal (D.P i j) * ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) :=
            Finset.sum_le_sum fun j _ => by gcongr; exact hstep j
        _ = (∑ j : Fin L, ENNReal.ofReal (D.P i j)) * ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) :=
            (Finset.sum_mul ..).symm
        _ = ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP_nonneg hD i j), hP_sum hD i,
              ENNReal.ofReal_one, one_mul]
    have halg : D.C * (1 + |x|) + α * (A * (1 + |x|) + B + A * Mp) = A * (1 + |x|) + B := by
      have h1α : 1 - α ≠ 0 := by linarith
      simp only [A, B, growthA, growthB]
      field_simp
      ring
    calc ENNReal.ofReal (D.f n i x) + ENNReal.ofReal α *
            ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
              ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * Jtrunc D α (n + 1) k j (x - z) zeroPolicy
        ≤ ENNReal.ofReal (D.C * (1 + |x|)) + ENNReal.ofReal α * ENNReal.ofReal (A * (1 + |x|) + B + A * Mp) := by
          gcongr
          exact hf_growth hD n i x
      _ = ENNReal.ofReal (D.C * (1 + |x|) + α * (A * (1 + |x|) + B + A * Mp)) := by
          rw [← ENNReal.ofReal_mul hα0.le, ← ENNReal.ofReal_add (by have := hC_pos hD; positivity) (by positivity)]
      _ = ENNReal.ofReal (A * (1 + |x|) + B) := by rw [halg]

lemma w_le_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    w D α n i x ≤ ENNReal.ofReal (growthC D α * (1 + |x|)) := by
  have h1 : growthA D α * (1 + |x|) + growthB D α ≤ growthC D α * (1 + |x|) := by
    unfold growthC
    have hB := growthB_nonneg hD hα0 hα1
    have hge : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
    nlinarith
  exact (iSup_le fun k => Jtrunc_zeroPolicy_le hD hα0 hα1 k n i x).trans (ENNReal.ofReal_le_ofReal h1)

lemma vTrunc_le_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    vTrunc D α n k i x ≤ ENNReal.ofReal (growthC D α * (1 + |x|)) :=
  ((theorem_6_1_eq_6_8 D α hD hα0 hα1).2.2 n k i x).trans (w_le_growth hD hα0 hα1 n i x)

lemma vLim_le_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    vLim D α n i x ≤ ENNReal.ofReal (growthC D α * (1 + |x|)) :=
  iSup_le fun k => vTrunc_le_growth hD hα0 hα1 n k i x

lemma vTrunc_ne_top {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) : vTrunc D α n k i x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (vTrunc_le_growth hD hα0 hα1 n k i x)

lemma vLim_ne_top {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) : vLim D α n i x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (vLim_le_growth hD hα0 hα1 n i x)

lemma vTrunc_toReal_le_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    (vTrunc D α n k i x).toReal ≤ growthC D α * (1 + |x|) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (vTrunc_le_growth hD hα0 hα1 n k i x)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (growthC_pos hD hα0 hα1).le (by positivity))] at h

lemma vLim_toReal_le_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    (vLim D α n i x).toReal ≤ growthC D α * (1 + |x|) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (vLim_le_growth hD hα0 hα1 n i x)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (growthC_pos hD hα0 hα1).le (by positivity))] at h

lemma vTrunc_mono_k {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) : Monotone (fun k => vTrunc D α n k i x) :=
  monotone_nat_of_le_succ fun k => (theorem_6_1_eq_6_8 D α hD hα0 hα1).2.1 n k i x

lemma vTrunc_toReal_le_vLim_toReal {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (n k : ℕ) (i : Fin L) (x : ℝ) :
    (vTrunc D α n k i x).toReal ≤ (vLim D α n i x).toReal :=
  ENNReal.toReal_mono (vLim_ne_top hD hα0 hα1 n i x) (le_iSup (fun m => vTrunc D α n m i x) k)

lemma lipschitz_uniformContinuous {f : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x x', |f x' - f x| ≤ K * |x' - x|) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε / (K + 1), div_pos hε (by linarith), fun {x y} hxy => ?_⟩
  rw [Real.dist_eq] at hxy ⊢
  calc |f x - f y| ≤ K * |x - y| := hf y x
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hxy.le hK
    _ < (K + 1) * (ε / (K + 1)) := by
      exact mul_lt_mul_of_pos_right (by linarith) (div_pos hε (by linarith))
    _ = ε := by
      have hK1 : K + 1 ≠ 0 := by linarith
      field_simp

lemma vTrunc_cont {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) : Continuous (fun x => (vTrunc D α n k i x).toReal) :=
  (lipschitz_uniformContinuous (growthA_pos hD hα1).le fun x x' => by
    simpa [growthA, div_mul_eq_mul_div] using (appendix_lipschitz D α hD hα0 hα1).1 n k i x x').continuous

lemma vLim_ucont {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) : UniformContinuous (fun x => (vLim D α n i x).toReal) :=
  lipschitz_uniformContinuous (growthA_pos hD hα1).le fun x x' => by
    simpa [growthA, div_mul_eq_mul_div] using (appendix_lipschitz D α hD hα0 hα1).2 n i x x'

/-- Part 1 of Theorem 6.1 (6.10): `v_n ∈ C_1` for every `n`. -/
theorem vLim_inC1 {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) : InC1 (fun i x => (vLim D α n i x).toReal) := by
  refine ⟨⟨⟨fun i x => ENNReal.toReal_nonneg,
    ⟨fun _ i x => (vLim D α n i x).toReal,
      fun _ i => (vLim_ucont hD hα0 hα1 n i).continuous,
      fun _ _ _ => ENNReal.toReal_nonneg,
      fun _ _ => tendsto_const_nhds⟩⟩,
    ⟨growthC D α, growthC_pos hD hα0 hα1, fun i x => vLim_toReal_le_growth hD hα0 hα1 n i x⟩⟩,
    fun i => vLim_ucont hD hα0 hα1 n i⟩

lemma f_le_vTrunc_one {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (m : ℕ) (j : Fin L) (y : ℝ) :
    ENNReal.ofReal (D.f m j y) ≤ vTrunc D α m 1 j y := by
  refine le_iInf₂ fun U hU => ?_
  rw [Jtrunc_cons hD hα0.le m 0 j y U hU]
  refine le_trans ?_ le_self_add
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (orderCost_nonneg hD (hU.1 0 _ _)))

lemma f_le_vTrunc_toReal {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (m : ℕ) {k : ℕ} (hk : 1 ≤ k) (j : Fin L) (y : ℝ) :
    D.f m j y ≤ (vTrunc D α m k j y).toReal := by
  have h1 : ENNReal.ofReal (D.f m j y) ≤ vTrunc D α m k j y :=
    (f_le_vTrunc_one hD hα0 m j y).trans (vTrunc_mono_k hD hα0 hα1 m j y hk)
  have h2 := ENNReal.toReal_mono (vTrunc_ne_top hD hα0 hα1 m k j y) h1
  rwa [ENNReal.toReal_ofReal (hf_nonneg hD m j y)] at h2

lemma f_le_vLim_toReal {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (m : ℕ) (j : Fin L) (y : ℝ) :
    D.f m j y ≤ (vLim D α m j y).toReal :=
  (f_le_vTrunc_toReal hD hα0 hα1 m le_rfl j y).trans
    (vTrunc_toReal_le_vLim_toReal hD hα0 hα1 m 1 j y)

/-! ### Section 4: Properties of `Fnext` -/

lemma Fnext_integrable {D : Model L} (hD : Standing D) {b : Fin L → ℝ → ℝ}
    (hnn : ∀ j x, 0 ≤ b j x) (hm : ∀ j, Measurable (b j))
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hgr : ∀ j x, b j x ≤ Cb * (1 + |x|))
    (n : ℕ) (i j : Fin L) (y : ℝ) :
    Integrable (fun z : ℝ => b j (y - z) * D.φ n i z) volume := by
  refine ⟨(((hm j).comp (measurable_const.sub measurable_id)).mul (hφ_meas hD n i)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
    mul_nonneg (hnn j (y - z)) (hφ_nonneg hD n i z))]
  have hpoint : ∀ z : ℝ,
      ENNReal.ofReal (b j (y - z) * D.φ n i z) ≤
        ENNReal.ofReal (Cb * (1 + |y|)) * ENNReal.ofReal (D.φ n i z) +
          ENNReal.ofReal Cb * ENNReal.ofReal (z * D.φ n i z) := by
    intro z
    by_cases hz : z < 0
    · simp [hφ_neg hD n i hz]
    · push Not at hz
      have habs : |y - z| ≤ |y| + z := (abs_sub y z).trans_eq (by rw [abs_of_nonneg hz])
      have h1 : b j (y - z) * D.φ n i z ≤ Cb * (1 + |y|) * D.φ n i z + Cb * (z * D.φ n i z) := by
        have h2 := hgr j (y - z)
        have hφ := hφ_nonneg hD n i z
        have h3 : b j (y - z) ≤ Cb * (1 + |y| + z) := by nlinarith
        have h4 := mul_le_mul_of_nonneg_right h3 hφ
        linarith
      have hφ := hφ_nonneg hD n i z
      have hnn1 : 0 ≤ Cb * (1 + |y|) := mul_nonneg hCb (by positivity)
      refine (ENNReal.ofReal_le_ofReal h1).trans ?_
      rw [ENNReal.ofReal_add (mul_nonneg hnn1 hφ) (mul_nonneg hCb (mul_nonneg hz hφ)),
        ENNReal.ofReal_mul hnn1, ENNReal.ofReal_mul (q := z * D.φ n i z) hCb]
  have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
    ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
  have hm1 : Measurable (fun z : ℝ => ENNReal.ofReal (Cb * (1 + |y|)) * ENNReal.ofReal (D.φ n i z)) :=
    hmφ.const_mul _
  have hm2 : Measurable (fun z : ℝ => ENNReal.ofReal (z * D.φ n i z)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.mul (hφ_meas hD n i))
  calc ∫⁻ z, ENNReal.ofReal (b j (y - z) * D.φ n i z)
      ≤ ∫⁻ z, (ENNReal.ofReal (Cb * (1 + |y|)) * ENNReal.ofReal (D.φ n i z) +
          ENNReal.ofReal Cb * ENNReal.ofReal (z * D.φ n i z)) := lintegral_mono hpoint
    _ = ENNReal.ofReal (Cb * (1 + |y|)) * (∫⁻ z, ENNReal.ofReal (D.φ n i z)) +
          ENNReal.ofReal Cb * (∫⁻ z, ENNReal.ofReal (z * D.φ n i z)) := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hmφ, lintegral_const_mul _ hm2]
    _ ≤ ENNReal.ofReal (Cb * (1 + |y|)) * 1 + ENNReal.ofReal Cb * ENNReal.ofReal D.M := by
        rw [hφ_int hD n i]; gcongr; exact hφ_mean hD n i
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨by simp, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩

lemma Fnext_nonneg {D : Model L} (hD : Standing D) {b : Fin L → ℝ → ℝ}
    (hnn : ∀ j x, 0 ≤ b j x) (n : ℕ) (i : Fin L) (y : ℝ) :
    0 ≤ Fnext D n b i y := by
  unfold Fnext
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hP_nonneg hD i j) ?_
  exact setIntegral_nonneg measurableSet_Ioi fun z _ => mul_nonneg (hnn j (y - z)) (hφ_nonneg hD n i z)

lemma Fnext_eq_lintegral {D : Model L} (hD : Standing D) {b : Fin L → ℝ → ℝ}
    (hnn : ∀ j x, 0 ≤ b j x) (hm : ∀ j, Measurable (b j))
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hgr : ∀ j x, b j x ≤ Cb * (1 + |x|))
    (n : ℕ) (i : Fin L) (y : ℝ) :
    ENNReal.ofReal (Fnext D n b i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (y - z)) := by
  unfold Fnext
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hP_nonneg hD i j)
    (setIntegral_nonneg measurableSet_Ioi fun z _ => mul_nonneg (hnn j _) (hφ_nonneg hD n i z))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (hP_nonneg hD i j)]
  congr 1
  have hIoi : ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z =
      ∫ z : ℝ, b j (y - z) * D.φ n i z := by
    rw [setIntegral_congr_set Ioi_ae_eq_Ici]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      have hlt : z < 0 := not_le.mp hz
      simp [hφ_neg hD n i hlt]
  rw [hIoi, ofReal_integral_eq_lintegral_ofReal (Fnext_integrable hD hnn hm hCb hgr n i j y)
    (Eventually.of_forall fun z => mul_nonneg (hnn j (y - z)) (hφ_nonneg hD n i z))]
  refine lintegral_congr fun z => ?_
  rw [mul_comm, ENNReal.ofReal_mul (hφ_nonneg hD n i z)]

lemma Fnext_mono {D : Model L} (hD : Standing D) {b₁ b₂ : Fin L → ℝ → ℝ}
    (hnn₁ : ∀ j x, 0 ≤ b₁ j x) (hm₁ : ∀ j, Measurable (b₁ j))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hgr₁ : ∀ j x, b₁ j x ≤ C₁ * (1 + |x|))
    (hnn₂ : ∀ j x, 0 ≤ b₂ j x) (hm₂ : ∀ j, Measurable (b₂ j))
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hgr₂ : ∀ j x, b₂ j x ≤ C₂ * (1 + |x|))
    (hle : ∀ j x, b₁ j x ≤ b₂ j x) (n : ℕ) (i : Fin L) (y : ℝ) :
    Fnext D n b₁ i y ≤ Fnext D n b₂ i y := by
  rw [← ENNReal.ofReal_le_ofReal_iff (Fnext_nonneg hD hnn₂ n i y),
    Fnext_eq_lintegral hD hnn₁ hm₁ hC₁ hgr₁, Fnext_eq_lintegral hD hnn₂ hm₂ hC₂ hgr₂]
  refine Finset.sum_le_sum fun j _ => ?_
  gcongr
  exact hle j _

lemma Fnext_lipschitz {D : Model L} (hD : Standing D) {b : Fin L → ℝ → ℝ}
    (hnn : ∀ j x, 0 ≤ b j x) (hm : ∀ j, Measurable (b j))
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hgr : ∀ j x, b j x ≤ Cb * (1 + |x|))
    {Lb : ℝ} (hLb : 0 ≤ Lb) (hlip : ∀ j x x', |b j x' - b j x| ≤ Lb * |x' - x|)
    (n : ℕ) (i : Fin L) (y y' : ℝ) :
    |Fnext D n b i y' - Fnext D n b i y| ≤ Lb * |y' - y| := by
  have h1 : ∀ u v : ℝ, Fnext D n b i v ≤ Fnext D n b i u + Lb * |v - u| := by
    intro u v
    have hnnv := Fnext_nonneg hD hnn n i v
    have hnnu := Fnext_nonneg hD hnn n i u
    have hnnr : 0 ≤ Lb * |v - u| := mul_nonneg hLb (abs_nonneg _)
    rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hnnu hnnr),
      ENNReal.ofReal_add hnnu hnnr,
      Fnext_eq_lintegral hD hnn hm hCb hgr n i v,
      Fnext_eq_lintegral hD hnn hm hCb hgr n i u]
    have hstep : ∀ j : Fin L,
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (v - z)) ≤
          (∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (u - z))) +
            ENNReal.ofReal (Lb * |v - u|) := by
      intro j
      have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
      calc ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (v - z))
          ≤ ∫⁻ z, (ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (u - z)) +
              ENNReal.ofReal (Lb * |v - u|) * ENNReal.ofReal (D.φ n i z)) := by
            refine lintegral_mono fun z => ?_
            have hb : b j (v - z) ≤ b j (u - z) + Lb * |v - u| := by
              have := hlip j (u - z) (v - z)
              have e : (v - z) - (u - z) = v - u := by ring
              rw [e, abs_le] at this
              linarith
            calc ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (v - z))
                ≤ ENNReal.ofReal (D.φ n i z) *
                    (ENNReal.ofReal (b j (u - z)) + ENNReal.ofReal (Lb * |v - u|)) := by
                  gcongr
                  exact (ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_add_le
              _ = _ := by ring
        _ = (∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (u - z))) +
              ENNReal.ofReal (Lb * |v - u|) := by
            rw [lintegral_add_right _ (hmφ.const_mul _), lintegral_const_mul _ hmφ,
              hφ_int hD n i, mul_one]
    calc ∑ j, ENNReal.ofReal (D.P i j) *
            ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (v - z))
        ≤ ∑ j, ENNReal.ofReal (D.P i j) *
            ((∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (u - z))) +
              ENNReal.ofReal (Lb * |v - u|)) := Finset.sum_le_sum fun j _ => by gcongr; exact hstep j
      _ = (∑ j, ENNReal.ofReal (D.P i j) *
            ∫⁻ z, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (u - z))) +
          (∑ j, ENNReal.ofReal (D.P i j)) * ENNReal.ofReal (Lb * |v - u|) := by
          simp_rw [mul_add]; rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP_nonneg hD i j), hP_sum hD i,
            ENNReal.ofReal_one, one_mul]
  rw [abs_le]
  have ha := h1 y y'
  have hb := h1 y' y
  rw [abs_sub_comm y y'] at hb
  constructor <;> linarith

lemma Fnext_vTrunc_tendsto {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (y : ℝ) :
    Tendsto (fun k => Fnext D n (fun j x => (vTrunc D α (n + 1) k j x).toReal) i y)
      atTop (𝓝 (Fnext D n (fun j x => (vLim D α (n + 1) j x).toReal) i y)) := by
  have hC := (growthC_pos hD hα0 hα1).le
  have hofk : ∀ k, ENNReal.ofReal (Fnext D n (fun j x => (vTrunc D α (n + 1) k j x).toReal) i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z) := by
    intro k
    rw [Fnext_eq_lintegral hD (fun _ _ => ENNReal.toReal_nonneg)
      (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable) hC
      (fun j x => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 (n + 1) k j (y - z))]
  have hoflim : ENNReal.ofReal (Fnext D n (fun j x => (vLim D α (n + 1) j x).toReal) i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vLim D α (n + 1) j (y - z) := by
    rw [Fnext_eq_lintegral hD (fun _ _ => ENNReal.toReal_nonneg)
      (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable) hC
      (fun j x => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_toReal (vLim_ne_top hD hα0 hα1 (n + 1) j (y - z))]
  have hterm : ∀ j : Fin L,
      Tendsto (fun k => ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z))
      atTop (𝓝 (ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vLim D α (n + 1) j (y - z))) := by
    intro j
    have hsup : (⨆ k : ℕ, ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z)) =
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vLim D α (n + 1) j (y - z) := by
      have hm : ∀ k, Measurable (fun z : ℝ =>
          ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z)) := fun k => by
        have heq : (fun z : ℝ => ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z)) =
            fun z => ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal ((vTrunc D α (n + 1) k j (y - z)).toReal) :=
          funext fun z => by rw [ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 _ _ _ _)]
        rw [heq]
        exact (ENNReal.measurable_ofReal.comp (hφ_meas hD n i)).mul
          (ENNReal.measurable_ofReal.comp
            ((vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable.comp (measurable_const.sub measurable_id)))
      have hmono : Monotone (fun k z =>
          ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z)) := fun a b hab z =>
        mul_le_mul' le_rfl (vTrunc_mono_k hD hα0 hα1 (n + 1) j (y - z) hab)
      rw [← lintegral_iSup hm hmono]
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.mul_iSup]; rfl
    have hmono_int : Monotone (fun k =>
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (y - z)) :=
      fun a b hab => lintegral_mono fun z =>
        mul_le_mul' le_rfl (vTrunc_mono_k hD hα0 hα1 (n + 1) j (y - z) hab)
    have ht := hsup ▸ tendsto_atTop_iSup hmono_int
    exact ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  have hsum_t : Tendsto (fun k => ENNReal.ofReal (Fnext D n (fun j x => (vTrunc D α (n + 1) k j x).toReal) i y))
      atTop (𝓝 (ENNReal.ofReal (Fnext D n (fun j x => (vLim D α (n + 1) j x).toReal) i y))) := by
    simp_rw [hofk, hoflim]
    exact tendsto_finsetSum _ fun j _ => hterm j
  have htoReal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hsum_t
  rw [ENNReal.toReal_ofReal (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i y)] at htoReal
  refine htoReal.congr fun k => ?_
  exact ENNReal.toReal_ofReal (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i y)

/-! ### Section 5: Truncated Bellman & Infinite-Horizon Bellman (`BellmanInf`) -/

lemma bddBelow_bellman_rhs {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    {b : Fin L → ℝ → ℝ} (hnn : ∀ j x, 0 ≤ b j x) (n : ℕ) (i : Fin L) (x : ℝ) :
    BddBelow (Set.range fun u : {u : ℝ // 0 ≤ u} =>
      orderCost D n i u + α * Fnext D n b i (x + u)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact add_nonneg (orderCost_nonneg hD u.2) (mul_nonneg hα0.le (Fnext_nonneg hD hnn n i _))

lemma vTrunc_bellman_ge {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D n i u + α * Fnext D n (fun j y => (vTrunc D α (n + 1) k j y).toReal) i (x + u)) ≤
      (vTrunc D α n (k + 1) i x).toReal := by
  set b := fun j y => (vTrunc D α (n + 1) k j y).toReal
  set I := ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + α * Fnext D n b i (x + u))
  have hI0 : 0 ≤ I := le_ciInf fun u =>
    add_nonneg (orderCost_nonneg hD u.2) (mul_nonneg hα0.le (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _))
  have hC := (growthC_pos hD hα0 hα1).le
  have hle : ENNReal.ofReal (D.f n i x + I) ≤ vTrunc D α n (k + 1) i x := by
    refine le_iInf₂ fun U hU => ?_
    rw [Jtrunc_cons hD hα0.le n k i x U hU]
    set u₀ : {u : ℝ // 0 ≤ u} := ⟨U 0 (fun _ => i) Fin.elim0, hU.1 0 _ _⟩
    have hFb : ENNReal.ofReal (Fnext D n b i (x + u₀)) =
        ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u₀ - z) := by
      rw [Fnext_eq_lintegral hD (fun _ _ => ENNReal.toReal_nonneg)
        (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable) hC
        (fun j y => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j y)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; refine lintegral_congr fun z => ?_
      rw [ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 (n + 1) k j (x + u₀ - z))]
    have hinf : I ≤ orderCost D n i u₀ + α * Fnext D n b i (x + u₀) :=
      ciInf_le (bddBelow_bellman_rhs hD hα0 (fun _ _ => ENNReal.toReal_nonneg) n i x) u₀
    calc ENNReal.ofReal (D.f n i x + I)
        ≤ ENNReal.ofReal (D.f n i x + (orderCost D n i u₀ + α * Fnext D n b i (x + u₀))) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal ((orderCost D n i u₀ + D.f n i x) + α * Fnext D n b i (x + u₀)) := by ring_nf
      _ = ENNReal.ofReal (orderCost D n i u₀ + D.f n i x) +
            ENNReal.ofReal α * ENNReal.ofReal (Fnext D n b i (x + u₀)) := by
          rw [ENNReal.ofReal_add (add_nonneg (orderCost_nonneg hD u₀.2) (hf_nonneg hD n i x))
            (mul_nonneg hα0.le (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _)),
            ENNReal.ofReal_mul hα0.le]
      _ = ENNReal.ofReal (orderCost D n i u₀ + D.f n i x) +
            ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
              ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u₀ - z) := by
          rw [hFb]
      _ ≤ _ := by
          gcongr with j _ z
          exact iInf₂_le (shiftPolicy U i z) (shiftPolicy_adm hU i z)
  have htr := ENNReal.toReal_mono (vTrunc_ne_top hD hα0 hα1 n (k + 1) i x) hle
  rwa [ENNReal.toReal_ofReal (add_nonneg (hf_nonneg hD n i x) hI0)] at htr

/-- Measurability of a countable `ℤ`-indexed piecewise family. -/
lemma measurable_int_piecewise {α : Type*} [MeasurableSpace α]
    {m : α → ℤ} (hm : Measurable m) {F : ℤ → α → ℝ} (hF : ∀ q, Measurable (F q)) :
    Measurable (fun a => F (m a) a) := by
  intro s hs
  have heq : (fun a => F (m a) a) ⁻¹' s = ⋃ q : ℤ, (m ⁻¹' {q}) ∩ (F q ⁻¹' s) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨m a, rfl, h⟩, fun ⟨q, hq, h⟩ => hq ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q => (hm (measurableSet_singleton q)).inter (hF q hs)

lemma vTrunc_bellman_le_point {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x u : ℝ) (hu : 0 ≤ u) :
    (vTrunc D α n (k + 1) i x).toReal ≤
      D.f n i x + orderCost D n i u +
        α * Fnext D n (fun j y => (vTrunc D α (n + 1) k j y).toReal) i (x + u) := by
  set b := fun j y => (vTrunc D α (n + 1) k j y).toReal
  set A := growthA D α
  have hA : 0 < A := growthA_pos hD hα1
  have hC := (growthC_pos hD hα0 hα1).le
  -- Prove for every `ε > 0` that LHS ≤ RHS + α * ε
  suffices hε : ∀ ε : ℝ, 0 < ε →
      vTrunc D α n (k + 1) i x ≤
        ENNReal.ofReal (D.f n i x + orderCost D n i u + α * Fnext D n b i (x + u) + α * ε) by
    have htr : ∀ ε : ℝ, 0 < ε →
        (vTrunc D α n (k + 1) i x).toReal ≤
          D.f n i x + orderCost D n i u + α * Fnext D n b i (x + u) + α * ε := by
      intro ε hεp
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hε ε hεp)
      have hnn : 0 ≤ D.f n i x + orderCost D n i u + α * Fnext D n b i (x + u) + α * ε :=
        add_nonneg (add_nonneg (add_nonneg (hf_nonneg hD n i x) (orderCost_nonneg hD hu))
          (mul_nonneg hα0.le (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _)))
          (mul_nonneg hα0.le hεp.le)
      rwa [ENNReal.toReal_ofReal hnn] at h1
    by_contra hgt
    push Not at hgt
    set gap := (vTrunc D α n (k + 1) i x).toReal -
      (D.f n i x + orderCost D n i u + α * Fnext D n b i (x + u))
    have hgap : 0 < gap := sub_pos.mpr hgt
    have := htr (gap / (2 * α)) (div_pos hgap (by positivity))
    have e : α * (gap / (2 * α)) = gap / 2 := by field_simp
    linarith
  intro ε hεp
  set δ := ε / (4 * A)
  have hδ : 0 < δ := div_pos hεp (by positivity)
  -- For each `(j, q : ℤ)` choose an admissible policy within `ε / 2` of `vTrunc` at `q * δ`
  have hex : ∀ (j : Fin L) (q : ℤ), ∃ W : Policy L, Admissible W ∧
      Jtrunc D α (n + 1) k j ((q : ℝ) * δ) W ≤
        vTrunc D α (n + 1) k j ((q : ℝ) * δ) + ENNReal.ofReal (ε / 2) := by
    intro j q
    have hlt : vTrunc D α (n + 1) k j ((q : ℝ) * δ) <
        vTrunc D α (n + 1) k j ((q : ℝ) * δ) + ENNReal.ofReal (ε / 2) := by
      refine ENNReal.lt_add_right (vTrunc_ne_top hD hα0 hα1 (n + 1) k j _) ?_
      simp [ENNReal.ofReal_eq_zero, not_le.mpr (half_pos hεp)]
    rcases (iInf_lt_iff.mp hlt) with ⟨W, hW⟩
    rcases (iInf_lt_iff.mp hW) with ⟨hWadm, hWle⟩
    exact ⟨W, hWadm, hWle.le⟩
  choose W hWadm hWle using hex
  -- Stitch `W` into a single admissible policy `U`
  let U : Policy L := fun t =>
    match t with
    | 0 => fun _ _ => u
    | t + 1 => fun σ ξ => W (σ 1) ⌊(x + u - ξ 0) / δ⌋ t (Fin.tail σ) (Fin.tail ξ)
  have hUadm : Admissible U := by
    refine ⟨fun t σ ξ => ?_, fun t σ => ?_⟩
    · cases t with
      | zero => exact hu
      | succ t => exact (hWadm _ _).1 _ _ _
    · cases t with
      | zero => exact measurable_const
      | succ t =>
        have hm_idx : Measurable (fun ξ : Fin (t + 1) → ℝ => ⌊(x + u - ξ 0) / δ⌋) := by
          have h1 : Measurable (fun ξ : Fin (t + 1) → ℝ => x + u - ξ 0) :=
            measurable_const.sub (measurable_pi_apply (0 : Fin (t + 1)))
          exact Int.measurable_floor.comp (h1.div_const δ)
        exact measurable_int_piecewise hm_idx fun q =>
          ((hWadm (σ 1) q).2 t (Fin.tail σ)).comp meas_tail
  -- Bound `Jtrunc` of `shiftPolicy U i z` for every `j, z`
  have hshift_bound : ∀ (j : Fin L) (z : ℝ),
      Jtrunc D α (n + 1) k j (x + u - z) (shiftPolicy U i z) ≤
        vTrunc D α (n + 1) k j (x + u - z) + ENNReal.ofReal ε := by
    intro j z
    set y := x + u - z
    set q : ℤ := ⌊y / δ⌋
    have hcongr : Jtrunc D α (n + 1) k j y (shiftPolicy U i z) =
        Jtrunc D α (n + 1) k j y (W j q) := by
      refine Jtrunc_congr_start D α (n + 1) k j y fun t σ ξ hσ => ?_
      change W ((Fin.cons i σ : Fin (t + 2) → Fin L) 1)
          ⌊(x + u - (Fin.cons z ξ : Fin (t + 1) → ℝ) 0) / δ⌋ t
          (Fin.tail (Fin.cons i σ : Fin (t + 2) → Fin L))
          (Fin.tail (Fin.cons z ξ : Fin (t + 1) → ℝ)) = W j q t σ ξ
      have h1 : (Fin.cons i σ : Fin (t + 2) → Fin L) 1 = j := by
        simpa [Fin.cons_succ] using hσ
      simp [h1, Fin.tail_cons, y, q]
    rw [hcongr]
    have hdist : |y - (q : ℝ) * δ| ≤ δ := by
      have h1 : (q : ℝ) ≤ y / δ := Int.floor_le (y / δ)
      have h2 : y / δ < (q : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
      have h1' : (q : ℝ) * δ ≤ y := (le_div_iff₀ hδ).mp h1
      have h2' : y < ((q : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h2
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hAd : D.C * |y - (q : ℝ) * δ| / (1 - α) ≤ ε / 4 := by
      have e : D.C * |y - (q : ℝ) * δ| / (1 - α) = A * |y - (q : ℝ) * δ| := by
        simp [A, growthA]; ring
      rw [e]
      calc A * |y - (q : ℝ) * δ| ≤ A * δ := mul_le_mul_of_nonneg_left hdist hA.le
        _ = ε / 4 := by simp [δ]; field_simp
    have hAd' : D.C * |(q : ℝ) * δ - y| / (1 - α) ≤ ε / 4 := by
      rwa [abs_sub_comm]
    have hvshift : vTrunc D α (n + 1) k j ((q : ℝ) * δ) ≤
        vTrunc D α (n + 1) k j y + ENNReal.ofReal (ε / 4) := by
      have hlip := (appendix_lipschitz D α hD hα0 hα1).1 (n + 1) k j y ((q : ℝ) * δ)
      rw [abs_le] at hlip
      have hreal : (vTrunc D α (n + 1) k j ((q : ℝ) * δ)).toReal ≤
          (vTrunc D α (n + 1) k j y).toReal + ε / 4 := by linarith
      rw [← ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 (n + 1) k j ((q : ℝ) * δ)),
        ← ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 (n + 1) k j y),
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    calc Jtrunc D α (n + 1) k j y (W j q)
        ≤ Jtrunc D α (n + 1) k j ((q : ℝ) * δ) (W j q) +
            ENNReal.ofReal (D.C * |y - (q : ℝ) * δ| / (1 - α)) :=
          Jtrunc_shift hD hα0 hα1 (n + 1) k j ((q : ℝ) * δ) y (W j q)
      _ ≤ (vTrunc D α (n + 1) k j ((q : ℝ) * δ) + ENNReal.ofReal (ε / 2)) +
            ENNReal.ofReal (ε / 4) := by
          gcongr
          · exact hWle j q
      _ ≤ (vTrunc D α (n + 1) k j y + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2)) +
            ENNReal.ofReal (ε / 4) := by gcongr
      _ = vTrunc D α (n + 1) k j y + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4)) := by
          ring
      _ = vTrunc D α (n + 1) k j y + ENNReal.ofReal ε := by
          congr 1
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- Now plug `U` into `vTrunc ≤ Jtrunc U` and expand with `Jtrunc_cons`
  have hFb : ENNReal.ofReal (Fnext D n b i (x + u)) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u - z) := by
    rw [Fnext_eq_lintegral hD (fun _ _ => ENNReal.toReal_nonneg)
      (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable) hC
      (fun j y => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j y)]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 (n + 1) k j (x + u - z))]
  have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
    ENNReal.measurable_ofReal.comp (hφ_meas hD n i)
  have hu0 : U 0 (fun _ => i) Fin.elim0 = u := rfl
  calc vTrunc D α n (k + 1) i x
      ≤ Jtrunc D α n (k + 1) i x U := iInf₂_le U hUadm
    _ = ENNReal.ofReal (orderCost D n i u + D.f n i x) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
              Jtrunc D α (n + 1) k j (x + u - z) (shiftPolicy U i z) := by
        rw [Jtrunc_cons hD hα0.le n k i x U hUadm, hu0]
    _ ≤ ENNReal.ofReal (orderCost D n i u + D.f n i x) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ((∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u - z)) +
              ENNReal.ofReal ε) := by
        gcongr with j _
        calc ∫⁻ z, ENNReal.ofReal (D.φ n i z) *
                Jtrunc D α (n + 1) k j (x + u - z) (shiftPolicy U i z)
            ≤ ∫⁻ z, (ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u - z) +
                ENNReal.ofReal ε * ENNReal.ofReal (D.φ n i z)) := by
              refine lintegral_mono fun z => ?_
              calc ENNReal.ofReal (D.φ n i z) *
                      Jtrunc D α (n + 1) k j (x + u - z) (shiftPolicy U i z)
                  ≤ ENNReal.ofReal (D.φ n i z) * (vTrunc D α (n + 1) k j (x + u - z) + ENNReal.ofReal ε) := by
                    gcongr; exact hshift_bound j z
                _ = _ := by ring
          _ = (∫⁻ z, ENNReal.ofReal (D.φ n i z) * vTrunc D α (n + 1) k j (x + u - z)) +
                ENNReal.ofReal ε := by
              rw [lintegral_add_right _ (hmφ.const_mul _), lintegral_const_mul _ hmφ,
                hφ_int hD n i, mul_one]
    _ = ENNReal.ofReal (orderCost D n i u + D.f n i x) +
          ENNReal.ofReal α * (ENNReal.ofReal (Fnext D n b i (x + u)) + ENNReal.ofReal ε) := by
        congr 2
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP_nonneg hD i j), hP_sum hD i,
          ENNReal.ofReal_one, one_mul, hFb]
    _ = ENNReal.ofReal (D.f n i x + orderCost D n i u + α * Fnext D n b i (x + u) + α * ε) := by
        rw [← ENNReal.ofReal_add (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _) hεp.le,
          ← ENNReal.ofReal_mul hα0.le,
          ← ENNReal.ofReal_add (add_nonneg (orderCost_nonneg hD hu) (hf_nonneg hD n i x))
            (mul_nonneg hα0.le (add_nonneg (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _) hεp.le))]
        congr 1; ring

lemma vLim_bellman_le {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x : ℝ) :
    (vLim D α n i x).toReal ≤
      D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u + α * Fnext D n (fun j y => (vLim D α (n + 1) j y).toReal) i (x + u)) := by
  set vnext := fun j y => (vLim D α (n + 1) j y).toReal
  have hC := (growthC_pos hD hα0 hα1).le
  rw [← sub_le_iff_le_add']
  refine le_ciInf fun u => ?_
  rw [sub_le_iff_le_add']
  -- Show `vLim D α n i x ≤ ENNReal.ofReal (D.f n i x + orderCost D n i u + α * Fnext vnext (x + u))`
  have hbound : ∀ k : ℕ, vTrunc D α n k i x ≤
      ENNReal.ofReal (D.f n i x + (orderCost D n i u + α * Fnext D n vnext i (x + u))) := by
    intro k
    cases k with
    | zero =>
      rw [(theorem_6_1_eq_6_8 D α hD hα0 hα1).1 n i x]; exact bot_le
    | succ k =>
      have h1 := vTrunc_bellman_le_point hD hα0 hα1 n k i x u u.2
      have hF : Fnext D n (fun j y => (vTrunc D α (n + 1) k j y).toReal) i (x + u) ≤
          Fnext D n vnext i (x + u) :=
        Fnext_mono hD (fun _ _ => ENNReal.toReal_nonneg)
          (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable) hC
          (fun j y => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j y)
          (fun _ _ => ENNReal.toReal_nonneg)
          (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable) hC
          (fun j y => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j y)
          (fun j y => vTrunc_toReal_le_vLim_toReal hD hα0 hα1 (n + 1) k j y) n i (x + u)
      have h2 : (vTrunc D α n (k + 1) i x).toReal ≤
          D.f n i x + (orderCost D n i u + α * Fnext D n vnext i (x + u)) := by nlinarith
      rw [← ENNReal.ofReal_toReal (vTrunc_ne_top hD hα0 hα1 n (k + 1) i x)]
      exact ENNReal.ofReal_le_ofReal h2
  have hsup : vLim D α n i x ≤
      ENNReal.ofReal (D.f n i x + (orderCost D n i u + α * Fnext D n vnext i (x + u))) :=
    iSup_le hbound
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  have hnn : 0 ≤ D.f n i x + (orderCost D n i u + α * Fnext D n vnext i (x + u)) :=
    add_nonneg (hf_nonneg hD n i x)
      (add_nonneg (orderCost_nonneg hD u.2)
        (mul_nonneg hα0.le (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _)))
  rwa [ENNReal.toReal_ofReal hnn] at htr

/-- Coercivity from `Cond42`: `c^i_n y + α F_{n+1}(f_{n+1})(i, y) → +∞` as `y → +∞`. -/
lemma coercivity_f {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (i : Fin L) :
    Tendsto (fun y : ℝ => D.c n i * y + α * Fnext D n (D.f (n + 1)) i y) atTop atTop := by
  have hbase : Tendsto (fun y : ℝ => α * (D.c n i * y + Fnext D n (D.f (n + 1)) i y)) atTop atTop :=
    (h42 n i).const_mul_atTop hα0
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  have hc := hc_nonneg hD n i
  have hcy : 0 ≤ D.c n i * y := mul_nonneg hc hy
  nlinarith

lemma vLim_bellman_ge {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (i : Fin L) (x : ℝ) :
    D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D n i u + α * Fnext D n (fun j y => (vLim D α (n + 1) j y).toReal) i (x + u)) ≤
      (vLim D α n i x).toReal := by
  set vnext := fun j y => (vLim D α (n + 1) j y).toReal
  set vt := fun k j y => (vTrunc D α (n + 1) k j y).toReal
  set ψ : ℝ → ℝ := fun u => orderCost D n i u + α * Fnext D n vnext i (x + u)
  set ψk : ℕ → ℝ → ℝ := fun k u => orderCost D n i u + α * Fnext D n (vt k) i (x + u)
  set g : ℝ → ℝ := fun u => D.c n i * u + α * Fnext D n vnext i (x + u)
  set gk : ℕ → ℝ → ℝ := fun k u => D.c n i * u + α * Fnext D n (vt k) i (x + u)
  set M₀ := ψ 0
  have hC := (growthC_pos hD hα0 hα1).le
  have hA := (growthA_pos hD hα1).le
  -- Uniform coercivity: find `R ≥ 0` such that for all `u > R` and `k ≥ 1`, `ψk k u > M₀`
  have hcoerc : Tendsto (fun u : ℝ => D.c n i * u + α * Fnext D n (D.f (n + 1)) i (x + u)) atTop atTop := by
    have ht1 : Tendsto (fun u : ℝ => D.c n i * (x + u) + α * Fnext D n (D.f (n + 1)) i (x + u)) atTop atTop :=
      (coercivity_f hD h42 hα0 hα1 n i).comp (tendsto_atTop_add_const_left atTop x tendsto_id)
    have ht2 : Tendsto (fun u : ℝ => (D.c n i * (x + u) + α * Fnext D n (D.f (n + 1)) i (x + u)) + (- (D.c n i * x))) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ ht1
    refine ht2.congr fun u => by ring
  rcases (Filter.eventually_atTop.mp (hcoerc.eventually (eventually_gt_atTop M₀))) with ⟨R₀, hR₀⟩
  set R := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hR_bound : ∀ k : ℕ, 1 ≤ k → ∀ u : ℝ, R < u → M₀ < ψk k u := by
    intro k hk u hu
    have huR₀ : R₀ ≤ u := le_trans (le_max_left _ _) hu.le
    have h1 : M₀ < D.c n i * u + α * Fnext D n (D.f (n + 1)) i (x + u) := hR₀ u huR₀
    have hF : Fnext D n (D.f (n + 1)) i (x + u) ≤ Fnext D n (vt k) i (x + u) :=
      Fnext_mono hD (hf_nonneg hD (n + 1)) (fun j => (hf_cont hD (n + 1) j).measurable)
        (hC_pos hD).le (hf_growth hD (n + 1))
        (fun _ _ => ENNReal.toReal_nonneg) (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable)
        hC (fun j y => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j y)
        (fun j y => f_le_vTrunc_toReal hD hα0 hα1 (n + 1) hk j y) n i (x + u)
    have hKδ : 0 ≤ D.K n i * delta u := mul_nonneg (hK_nonneg hD n i) (delta_nonneg u)
    simp only [ψk, orderCost]
    nlinarith
  -- Uniform Lipschitz constant for `g` and `gk k`
  set Lg := D.c n i + α * growthA D α
  have hLg : 0 ≤ Lg := add_nonneg (hc_nonneg hD n i) (mul_nonneg hα0.le hA)
  have hg_lip : ∀ u₁ u₂, |g u₁ - g u₂| ≤ Lg * |u₁ - u₂| := by
    intro u₁ u₂
    have hFl := Fnext_lipschitz hD (fun _ _ => ENNReal.toReal_nonneg)
      (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable) hC
      (fun j y => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j y) hA
      (fun j y y' => by simpa [growthA, div_mul_eq_mul_div] using (appendix_lipschitz D α hD hα0 hα1).2 (n + 1) j y y')
      n i (x + u₂) (x + u₁)
    have e1 : (x + u₁) - (x + u₂) = u₁ - u₂ := by ring
    rw [e1] at hFl
    have e2 : g u₁ - g u₂ = D.c n i * (u₁ - u₂) + α * (Fnext D n vnext i (x + u₁) - Fnext D n vnext i (x + u₂)) := by
      simp [g]; ring
    rw [e2]
    calc |D.c n i * (u₁ - u₂) + α * (Fnext D n vnext i (x + u₁) - Fnext D n vnext i (x + u₂))|
        ≤ |D.c n i * (u₁ - u₂)| + |α * (Fnext D n vnext i (x + u₁) - Fnext D n vnext i (x + u₂))| :=
          abs_add_le _ _
      _ = D.c n i * |u₁ - u₂| + α * |Fnext D n vnext i (x + u₁) - Fnext D n vnext i (x + u₂)| := by
          rw [abs_mul, abs_of_nonneg (hc_nonneg hD n i), abs_mul, abs_of_pos hα0]
      _ ≤ D.c n i * |u₁ - u₂| + α * (growthA D α * |u₁ - u₂|) := by gcongr
      _ = Lg * |u₁ - u₂| := by simp [Lg]; ring
  have hgk_lip : ∀ k u₁ u₂, |gk k u₁ - gk k u₂| ≤ Lg * |u₁ - u₂| := by
    intro k u₁ u₂
    have hFl := Fnext_lipschitz hD (fun _ _ => ENNReal.toReal_nonneg)
      (fun j => (vTrunc_cont hD hα0 hα1 (n + 1) k j).measurable) hC
      (fun j y => vTrunc_toReal_le_growth hD hα0 hα1 (n + 1) k j y) hA
      (fun j y y' => by simpa [growthA, div_mul_eq_mul_div] using (appendix_lipschitz D α hD hα0 hα1).1 (n + 1) k j y y')
      n i (x + u₂) (x + u₁)
    have e1 : (x + u₁) - (x + u₂) = u₁ - u₂ := by ring
    rw [e1] at hFl
    have e2 : gk k u₁ - gk k u₂ = D.c n i * (u₁ - u₂) + α * (Fnext D n (vt k) i (x + u₁) - Fnext D n (vt k) i (x + u₂)) := by
      simp [gk]; ring
    rw [e2]
    calc |D.c n i * (u₁ - u₂) + α * (Fnext D n (vt k) i (x + u₁) - Fnext D n (vt k) i (x + u₂))|
        ≤ |D.c n i * (u₁ - u₂)| + |α * (Fnext D n (vt k) i (x + u₁) - Fnext D n (vt k) i (x + u₂))| :=
          abs_add_le _ _
      _ = D.c n i * |u₁ - u₂| + α * |Fnext D n (vt k) i (x + u₁) - Fnext D n (vt k) i (x + u₂)| := by
          rw [abs_mul, abs_of_nonneg (hc_nonneg hD n i), abs_mul, abs_of_pos hα0]
      _ ≤ D.c n i * |u₁ - u₂| + α * (growthA D α * |u₁ - u₂|) := by gcongr
      _ = Lg * |u₁ - u₂| := by simp [Lg]; ring
  -- Show `D.f n i x + ⨅ u, ψ u ≤ (vLim D α n i x).toReal + ε` for every `ε > 0`
  suffices hε : ∀ ε : ℝ, 0 < ε →
      D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u}, ψ u ≤ (vLim D α n i x).toReal + ε by
    by_contra hgt
    push Not at hgt
    set gap := (D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u}, ψ u) - (vLim D α n i x).toReal
    have := hε (gap / 2) (by linarith)
    linarith
  intro ε hεp
  -- Finite uniform mesh on `[0, R]` of size `N + 1` with step `R / N < ε / (3 * (Lg + 1))`
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (Lg + 1) * R / ε)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hstep : R / (N : ℝ) < ε / (3 * (Lg + 1)) := by
    rw [div_lt_iff₀ hNpos]
    have h1 := (div_lt_iff₀ hεp).mp hN
    have h2 : 0 < 3 * (Lg + 1) := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ h2]
    linarith
  -- For each grid point `m : Fin (N + 1)`, `gk k (m * R / N) → g (m * R / N)`
  have hgrid : ∀ m : Fin (N + 1), ∃ K₀ : ℕ, ∀ k ≥ K₀,
      g ((m : ℕ) * R / N) - gk k ((m : ℕ) * R / N) < ε / 3 := by
    intro m
    have ht : Tendsto (fun k => gk k ((m : ℕ) * R / N)) atTop (𝓝 (g ((m : ℕ) * R / N))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (Fnext_vTrunc_tendsto hD hα0 hα1 n i _))
    have hev := ht.eventually (Ioi_mem_nhds (by linarith : g ((m : ℕ) * R / N) - ε / 3 < g ((m : ℕ) * R / N)))
    rcases Filter.eventually_atTop.mp hev with ⟨K₀, hK₀⟩
    exact ⟨K₀, fun k hk => by have := hK₀ k hk; linarith⟩
  choose Kgrid hKgrid using hgrid
  set K₀ := max 1 (Finset.univ.sup Kgrid)
  have hK₀1 : 1 ≤ K₀ := le_max_left _ _
  -- Uniform bound on `[0, R]` at `k = K₀`
  have hunif : ∀ u : ℝ, 0 ≤ u → u ≤ R → ψ u ≤ ψk K₀ u + ε := by
    intro u hu0 huR
    set mNat := min N ⌊u * (N : ℝ) / R⌋₊
    have hmle : mNat ≤ N := Nat.min_le_left _ _
    set m : Fin (N + 1) := ⟨mNat, Nat.lt_succ_of_le hmle⟩
    set um := (mNat : ℝ) * R / (N : ℝ)
    have hdist : |u - um| ≤ R / (N : ℝ) := by
      have hfloor_le : (⌊u * (N : ℝ) / R⌋₊ : ℝ) ≤ u * (N : ℝ) / R :=
        Nat.floor_le (by positivity)
      by_cases hcase : ⌊u * (N : ℝ) / R⌋₊ ≤ N
      · have hm_eq : mNat = ⌊u * (N : ℝ) / R⌋₊ := Nat.min_eq_right hcase
        have hlt : u * (N : ℝ) / R < (mNat : ℝ) + 1 := by
          rw [hm_eq]; exact Nat.lt_floor_add_one _
        have hle' : um ≤ u := by
          simp only [um, hm_eq]
          rw [div_le_iff₀ hNpos]
          have := (le_div_iff₀ hRpos).mp hfloor_le
          linarith
        have hlt' : u < um + R / (N : ℝ) := by
          simp only [um]
          have h1 : u * (N : ℝ) < ((mNat : ℝ) + 1) * R := (div_lt_iff₀ hRpos).mp hlt
          have h2 : u < ((mNat : ℝ) + 1) * R / (N : ℝ) := (lt_div_iff₀ hNpos).mpr h1
          have e : ((mNat : ℝ) + 1) * R / (N : ℝ) = (mNat : ℝ) * R / (N : ℝ) + R / (N : ℝ) := by ring
          linarith
        rw [abs_of_nonneg (by linarith)]; linarith
      · push Not at hcase
        have hm_eq : mNat = N := Nat.min_eq_left hcase.le
        have hum : um = R := by simp only [um, hm_eq]; field_simp
        have hu_eq : u = R := by
          have hge : (N : ℝ) ≤ u * (N : ℝ) / R :=
            le_trans (by exact_mod_cast hcase.le) hfloor_le
          have hge' : (N : ℝ) * R ≤ u * (N : ℝ) := (le_div_iff₀ hRpos).mp hge
          have hge'' : R ≤ u := by nlinarith
          linarith
        rw [hu_eq, hum, sub_self, abs_zero]; positivity
    have hK_m : Kgrid m ≤ K₀ := le_trans (Finset.le_sup (f := Kgrid) (Finset.mem_univ m)) (le_max_right _ _)
    have h1 := hKgrid m K₀ hK_m
    have h2 := (abs_le.mp (hg_lip u um)).2
    have h3 := (abs_le.mp (hgk_lip K₀ um u)).2
    rw [abs_sub_comm um u] at h3
    have hLg_dist : Lg * |u - um| < ε / 3 := by
      calc Lg * |u - um| ≤ Lg * (R / (N : ℝ)) := mul_le_mul_of_nonneg_left hdist hLg
        _ ≤ (Lg + 1) * (R / (N : ℝ)) := by nlinarith [div_nonneg hRpos.le hNpos.le]
        _ < (Lg + 1) * (ε / (3 * (Lg + 1))) := mul_lt_mul_of_pos_left hstep (by positivity)
        _ = ε / 3 := by field_simp
    have hψ_diff : ψ u - ψk K₀ u = g u - gk K₀ u := by
      simp only [ψ, ψk, g, gk, orderCost]; ring
    linarith
  -- Now compare infimum of `ψ` with infimum of `ψk K₀`
  have hinf_le : (⨅ u : {u : ℝ // 0 ≤ u}, ψ u) ≤
      (⨅ u : {u : ℝ // 0 ≤ u}, ψk K₀ u) + ε := by
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun u => ?_
    rw [sub_le_iff_le_add]
    by_cases huR : u.1 ≤ R
    · exact (ciInf_le (bddBelow_bellman_rhs hD hα0 (fun _ _ => ENNReal.toReal_nonneg) n i x) u).trans
        (hunif u.1 u.2 huR)
    · push Not at huR
      have hM : M₀ < ψk K₀ u.1 := hR_bound K₀ hK₀1 u.1 huR
      have h0 : (⨅ v : {v : ℝ // 0 ≤ v}, ψ v) ≤ M₀ :=
        ciInf_le (bddBelow_bellman_rhs hD hα0 (fun _ _ => ENNReal.toReal_nonneg) n i x) ⟨0, le_rfl⟩
      linarith
  have hv := vTrunc_bellman_ge hD hα0 hα1 n K₀ i x
  have hvl := vTrunc_toReal_le_vLim_toReal hD hα0 hα1 n (K₀ + 1) i x
  linarith

/-- `vLim` satisfies the infinite-horizon Bellman equation (6.2). -/
theorem vLim_bellman {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    BellmanInf D α (fun n i x => (vLim D α n i x).toReal) :=
  fun n i x => le_antisymm (vLim_bellman_le hD hα0 hα1 n i x) (vLim_bellman_ge hD h42 hα0 hα1 n i x)

/-! ### Section 6: Existence of an `InB0` minimizer (Part 2) -/

/-- 1D Baire-class-1 optimal order selector for a coercive Lipschitz function `G` and fixed cost `K ≥ 0`. -/
lemma exists_inB0_minimizer_1d {G : ℝ → ℝ} {K LG : ℝ} (hK : 0 ≤ K) (hLG : 0 ≤ LG)
    (hGlip : ∀ y₁ y₂, |G y₁ - G y₂| ≤ LG * |y₁ - y₂|) (hGtop : Tendsto G atTop atTop) :
    ∃ u : ℝ → ℝ, (∀ x, 0 ≤ u x) ∧
      (∃ g : ℕ → ℝ → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m x, 0 ≤ g m x) ∧
        ∀ x, Tendsto (fun m => g m x) atTop (𝓝 (u x))) ∧
      ∀ x v : ℝ, 0 ≤ v → K * delta (u x) + G (x + u x) ≤ K * delta v + G (x + v) := by
  have hGcont : Continuous G := (lipschitz_uniformContinuous hLG fun x x' => hGlip x' x).continuous
  -- Step 1: `G` attains its minimum on `[x, ∞)` for every `x`
  have hatt : ∀ x : ℝ, ∃ y ∈ Set.Ici x, ∀ z ∈ Set.Ici x, G y ≤ G z := by
    intro x
    rcases Filter.eventually_atTop.mp (hGtop.eventually (eventually_ge_atTop (G x + 1))) with ⟨R₀, hR₀⟩
    set R := max x R₀
    have hxR : x ≤ R := le_max_left _ _
    obtain ⟨y, hyIcc, hymin⟩ :=
      isCompact_Icc.exists_isMinOn ⟨x, Set.left_mem_Icc.2 hxR⟩ hGcont.continuousOn
    refine ⟨y, hyIcc.1, fun z hz => ?_⟩
    by_cases hzR : z ≤ R
    · exact hymin ⟨hz, hzR⟩
    · push Not at hzR
      have hyx : G y ≤ G x := hymin (Set.left_mem_Icc.2 hxR)
      have hz1 : G x + 1 ≤ G z := hR₀ z (le_trans (le_max_right _ _) hzR.le)
      linarith
  -- Define `H x = sInf (G '' Ici x)` and `yStar x = sInf {y | x ≤ y ∧ G y = H x}`
  let H : ℝ → ℝ := fun x => sInf (G '' Set.Ici x)
  have hH_le : ∀ x y, x ≤ y → H x ≤ G y := by
    intro x y hxy
    obtain ⟨y₀, _, hy₀⟩ := hatt x
    refine csInf_le ⟨G y₀, ?_⟩ ⟨y, hxy, rfl⟩
    rintro _ ⟨z, hz, rfl⟩; exact hy₀ z hz
  have hH_exists : ∀ x, ∃ y, x ≤ y ∧ G y = H x := by
    intro x
    obtain ⟨y₀, hy₀Ici, hy₀⟩ := hatt x
    refine ⟨y₀, hy₀Ici, le_antisymm ?_ (hH_le x y₀ hy₀Ici)⟩
    refine le_csInf ⟨G x, x, Set.mem_Ici.mpr le_rfl, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩; exact hy₀ z hz
  have hH_mono : Monotone H := by
    intro x₁ x₂ h12
    obtain ⟨y₂, hy₂, hGy₂⟩ := hH_exists x₂
    rw [← hGy₂]; exact hH_le x₁ y₂ (h12.trans hy₂)
  have hH_lip : ∀ x₁ x₂, |H x₁ - H x₂| ≤ LG * |x₁ - x₂| := by
    have h1 : ∀ a b, H a ≤ H b + LG * |a - b| := by
      intro a b
      obtain ⟨yb, hyb, hGyb⟩ := hH_exists b
      set ya := yb + (a - b)
      have hya : a ≤ ya := by linarith
      have hle1 : H a ≤ G ya := hH_le a ya hya
      have hle2 : G ya - G yb ≤ LG * |ya - yb| := (abs_le.mp (hGlip ya yb)).2
      have e : ya - yb = a - b := by simp [ya]
      rw [e, hGyb] at hle2
      linarith
    intro x₁ x₂
    rw [abs_le]
    have ha := h1 x₁ x₂
    have hb := h1 x₂ x₁
    rw [abs_sub_comm x₂ x₁] at hb
    constructor <;> linarith
  have hH_cont : Continuous H := (lipschitz_uniformContinuous hLG fun x x' => hH_lip x' x).continuous
  let M : ℝ → Set ℝ := fun x => {y : ℝ | x ≤ y ∧ G y = H x}
  let yStar : ℝ → ℝ := fun x => sInf (M x)
  have hM_ne : ∀ x, (M x).Nonempty := fun x => hH_exists x
  have hM_bdd : ∀ x, BddBelow (M x) := fun x => ⟨x, fun _ hy => hy.1⟩
  have hM_closed : ∀ x, IsClosed (M x) := fun x =>
    isClosed_Ici.inter (isClosed_eq hGcont continuous_const)
  have hyStar_mem : ∀ x, yStar x ∈ M x := fun x => by
    have hcl := csInf_mem_closure (hM_ne x) (hM_bdd x)
    rwa [(hM_closed x).closure_eq] at hcl
  have hyStar_ge : ∀ x, x ≤ yStar x := fun x => (hyStar_mem x).1
  have hyStar_G : ∀ x, G (yStar x) = H x := fun x => (hyStar_mem x).2
  have hyStar_le : ∀ x y, x ≤ y → G y = H x → yStar x ≤ y :=
    fun x y hxy hGy => csInf_le (hM_bdd x) ⟨hxy, hGy⟩
  have hyStar_mono : Monotone yStar := by
    intro x₁ x₂ h12
    by_cases h : yStar x₁ ≤ x₂
    · exact h.trans (hyStar_ge x₂)
    · push Not at h
      have hH_eq : H x₂ = H x₁ :=
        le_antisymm ((hH_le x₂ (yStar x₁) h.le).trans_eq (hyStar_G x₁)) (hH_mono h12)
      exact hyStar_le x₁ (yStar x₂) (h12.trans (hyStar_ge x₂)) ((hyStar_G x₂).trans hH_eq)
  have hyStar_const : ∀ x t, x ≤ t → t ≤ yStar x → yStar t = yStar x := by
    intro x t hxt hty
    refine le_antisymm ?_ (hyStar_mono hxt)
    have hH_eq : H t = H x :=
      le_antisymm ((hH_le t (yStar x) hty).trans_eq (hyStar_G x)) (hH_mono hxt)
    exact hyStar_le t (yStar x) hty ((hyStar_G x).trans hH_eq.symm)
  -- Left continuity of `yStar` everywhere
  have hyStar_left : ∀ x, Tendsto yStar (𝓝[<] x) (𝓝 (yStar x)) := by
    intro x
    set Llim := sSup (yStar '' Set.Iio x)
    have ht : Tendsto yStar (𝓝[<] x) (𝓝 Llim) := hyStar_mono.tendsto_nhdsLT x
    have hL_le : Llim ≤ yStar x := by
      refine csSup_le ⟨yStar (x - 1), x - 1, by simp, rfl⟩ ?_
      rintro _ ⟨t, htlt, rfl⟩
      exact hyStar_mono (le_of_lt htlt)
    have hL_ge : x ≤ Llim := by
      by_contra hlt
      push Not at hlt
      have htx : (Llim + x) / 2 < x := by linarith
      have hLt : Llim < (Llim + x) / 2 := by linarith
      have hbdd : BddAbove (yStar '' Set.Iio x) :=
        ⟨yStar x, by rintro _ ⟨s, hs, rfl⟩; exact hyStar_mono (le_of_lt hs)⟩
      have htle : (Llim + x) / 2 ≤ Llim := (hyStar_ge _).trans (le_csSup hbdd ⟨_, htx, rfl⟩)
      linarith
    have hG_t1 : Tendsto (G ∘ yStar) (𝓝[<] x) (𝓝 (G Llim)) :=
      hGcont.continuousAt.tendsto.comp ht
    have hG_t2 : Tendsto (G ∘ yStar) (𝓝[<] x) (𝓝 (H x)) := by
      have heq : G ∘ yStar = H := funext hyStar_G
      rw [heq]
      exact hH_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hGL : G Llim = H x := tendsto_nhds_unique hG_t1 hG_t2
    have hEq : Llim = yStar x := le_antisymm hL_le (hyStar_le x Llim hL_ge hGL)
    rwa [hEq] at ht
  -- Continuity of `yStar` wherever `x < yStar x`
  have hyStar_contAt : ∀ x, x < yStar x → ContinuousAt yStar x := by
    intro x hlt
    rw [ContinuousAt, ← nhdsLT_sup_nhdsGE x, tendsto_sup]
    refine ⟨hyStar_left x, ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ico_mem_nhdsGE hlt] with t ⟨hxt, hty⟩
    exact (hyStar_const x t hxt hty.le).symm
  -- Open ordering region `A = {x | K + H x < G x}`
  let A : Set ℝ := {x : ℝ | K + H x < G x}
  have hA_open : IsOpen A := isOpen_lt (continuous_const.add hH_cont) hGcont
  let u : ℝ → ℝ := fun x => if K + H x < G x then yStar x - x else 0
  have hu_nonneg : ∀ x, 0 ≤ u x := by
    intro x; simp only [u]; split_ifs
    · linarith [hyStar_ge x]
    · exact le_rfl
  have hu_contAt_A : ∀ x ∈ A, ContinuousAt u x := by
    intro x hx
    have hx' : K + H x < G x := hx
    have hlt : x < yStar x := by
      have hHG : H x < G x := by linarith
      have hne : yStar x ≠ x := fun heq => by
        have := hyStar_G x; rw [heq] at this; linarith
      exact lt_of_le_of_ne (hyStar_ge x) hne.symm
    have hc : ContinuousAt (fun t => yStar t - t) x := (hyStar_contAt x hlt).sub continuousAt_id
    refine hc.congr ?_
    filter_upwards [hA_open.mem_nhds hx] with t ht
    simp [u, show K + H t < G t from ht]
  -- Construct the sequence `g m` of nonnegative continuous functions converging pointwise to `u`
  have hB0 : ∃ g : ℕ → ℝ → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m x, 0 ≤ g m x) ∧
      ∀ x, Tendsto (fun m => g m x) atTop (𝓝 (u x)) := by
    by_cases hAc : Aᶜ.Nonempty
    · let d : ℝ → ℝ := fun x => Metric.infDist x Aᶜ
      let ψ : ℕ → ℝ → ℝ := fun m t => max 0 (min 1 ((m : ℝ) * t - 1))
      let g : ℕ → ℝ → ℝ := fun m x => ψ m (d x) * u x
      have hd_cont : Continuous d := Metric.continuous_infDist_pt Aᶜ
      have hψ_cont : ∀ m, Continuous (ψ m) := fun m =>
        continuous_const.max (continuous_const.min ((continuous_const.mul continuous_id).sub continuous_const))
      refine ⟨g, fun m => continuous_iff_continuousAt.mpr fun x => ?_,
        fun m x => mul_nonneg (le_max_left _ _) (hu_nonneg x), fun x => ?_⟩
      · by_cases hx : x ∈ A
        · exact (((hψ_cont m).comp hd_cont).continuousAt).mul (hu_contAt_A x hx)
        · have hdx : d x = 0 := Metric.infDist_zero_of_mem hx
          have hopen : IsOpen {t : ℝ | d t < 1 / ((m : ℝ) + 1)} :=
            isOpen_lt hd_cont continuous_const
          have hmem : x ∈ {t : ℝ | d t < 1 / ((m : ℝ) + 1)} := by
            show d x < 1 / ((m : ℝ) + 1)
            rw [hdx]; positivity
          refine (continuousAt_const (y := (0 : ℝ))).congr ?_
          filter_upwards [hopen.mem_nhds hmem] with t ht
          have hmt : (m : ℝ) * d t < 1 := by
            have h1 : (m : ℝ) * d t ≤ (m : ℝ) * (1 / ((m : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg m)
            have h2 : (m : ℝ) * (1 / ((m : ℝ) + 1)) < 1 := by
              rw [mul_one_div, div_lt_one (by positivity)]; linarith
            linarith
          have hψ0 : ψ m (d t) = 0 := by
            simp only [ψ]
            apply max_eq_left
            exact (min_le_right _ _).trans (by linarith)
          simp [g, hψ0]
      · by_cases hx : x ∈ A
        · have hdx_pos : 0 < d x := (hA_open.isClosed_compl.notMem_iff_infDist_pos hAc).mp (by simpa using hx)
          obtain ⟨M₀, hM₀⟩ := exists_nat_ge (2 / d x)
          refine tendsto_atTop_of_eventually_const (i₀ := M₀) fun m hm => ?_
          have hmd : 2 ≤ (m : ℝ) * d x := by
            have h1 : 2 / d x ≤ (m : ℝ) := hM₀.trans (by exact_mod_cast hm)
            exact (div_le_iff₀ hdx_pos).mp h1
          have hψ1 : ψ m (d x) = 1 := by
            simp only [ψ]
            rw [min_eq_left (by linarith), max_eq_right zero_le_one]
          simp [g, hψ1]
        · refine tendsto_const_nhds.congr fun m => ?_
          have hu0 : u x = 0 := by simp [u, show ¬(K + H x < G x) from hx]
          simp [g, hu0]
    · rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hAc
      have huc : Continuous u := continuous_iff_continuousAt.mpr fun x =>
        hu_contAt_A x (by rw [hAc]; trivial)
      exact ⟨fun _ => u, fun _ => huc, fun _ => hu_nonneg, fun _ => tendsto_const_nhds⟩
  -- Optimality of `u x`
  refine ⟨u, hu_nonneg, hB0, fun x v hv => ?_⟩
  by_cases hx : K + H x < G x
  · have hlt : x < yStar x := by
      have hHG : H x < G x := by linarith
      have hne : yStar x ≠ x := fun heq => by have := hyStar_G x; rw [heq] at this; linarith
      exact lt_of_le_of_ne (hyStar_ge x) hne.symm
    have hux : u x = yStar x - x := if_pos hx
    have hpos : 0 < u x := by linarith
    rw [hux, delta_pos (by linarith : 0 < yStar x - x), mul_one, add_sub_cancel, hyStar_G x]
    rcases eq_or_lt_of_le hv with rfl | hvpos
    · rw [delta_zero, mul_zero, zero_add, add_zero]; linarith
    · rw [delta_pos hvpos, mul_one]
      linarith [hH_le x (x + v) (by linarith)]
  · push Not at hx
    have hux : u x = 0 := if_neg (not_lt.mpr hx)
    rw [hux, delta_zero, mul_zero, zero_add, add_zero]
    rcases eq_or_lt_of_le hv with rfl | hvpos
    · rw [delta_zero, mul_zero, zero_add, add_zero]
    · rw [delta_pos hvpos, mul_one]
      linarith [hH_le x (x + v) (by linarith)]

/-- Part 2 of Theorem 6.1 (6.10): existence of an `InB0` minimizer of (6.2). -/
theorem exists_inB0_attains {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ û : ℕ → Fin L → ℝ → ℝ, (∀ n, InB0 (û n)) ∧
      AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û := by
  set v := fun n i x => (vLim D α n i x).toReal
  have hC := (growthC_pos hD hα0 hα1).le
  have hA := (growthA_pos hD hα1).le
  have h1d : ∀ (n : ℕ) (i : Fin L),
      ∃ u : ℝ → ℝ, (∀ x, 0 ≤ u x) ∧
        (∃ g : ℕ → ℝ → ℝ, (∀ m, Continuous (g m)) ∧ (∀ m x, 0 ≤ g m x) ∧
          ∀ x, Tendsto (fun m => g m x) atTop (𝓝 (u x))) ∧
        ∀ x r : ℝ, 0 ≤ r →
          orderCost D n i (u x) + α * Fnext D n (v (n + 1)) i (x + u x) ≤
            orderCost D n i r + α * Fnext D n (v (n + 1)) i (x + r) := by
    intro n i
    let G : ℝ → ℝ := fun y => D.c n i * y + α * Fnext D n (v (n + 1)) i y
    set LG := D.c n i + α * growthA D α
    have hLG : 0 ≤ LG := add_nonneg (hc_nonneg hD n i) (mul_nonneg hα0.le hA)
    have hGlip : ∀ y₁ y₂, |G y₁ - G y₂| ≤ LG * |y₁ - y₂| := by
      intro y₁ y₂
      have hFl := Fnext_lipschitz hD (fun _ _ => ENNReal.toReal_nonneg)
        (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable) hC
        (fun j y => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j y) hA
        (fun j y y' => by simpa [growthA, div_mul_eq_mul_div] using (appendix_lipschitz D α hD hα0 hα1).2 (n + 1) j y y')
        n i y₂ y₁
      have e : G y₁ - G y₂ = D.c n i * (y₁ - y₂) + α * (Fnext D n (v (n + 1)) i y₁ - Fnext D n (v (n + 1)) i y₂) := by
        simp [G]; ring
      rw [e]
      calc |D.c n i * (y₁ - y₂) + α * (Fnext D n (v (n + 1)) i y₁ - Fnext D n (v (n + 1)) i y₂)|
          ≤ |D.c n i * (y₁ - y₂)| + |α * (Fnext D n (v (n + 1)) i y₁ - Fnext D n (v (n + 1)) i y₂)| :=
            abs_add_le _ _
        _ = D.c n i * |y₁ - y₂| + α * |Fnext D n (v (n + 1)) i y₁ - Fnext D n (v (n + 1)) i y₂| := by
            rw [abs_mul, abs_of_nonneg (hc_nonneg hD n i), abs_mul, abs_of_pos hα0]
        _ ≤ D.c n i * |y₁ - y₂| + α * (growthA D α * |y₁ - y₂|) := by gcongr
        _ = LG * |y₁ - y₂| := by simp [LG]; ring
    have hGtop : Tendsto G atTop atTop := by
      refine tendsto_atTop_mono (fun y => ?_) (coercivity_f hD h42 hα0 hα1 n i)
      have hF : Fnext D n (D.f (n + 1)) i y ≤ Fnext D n (v (n + 1)) i y :=
        Fnext_mono hD (hf_nonneg hD (n + 1)) (fun j => (hf_cont hD (n + 1) j).measurable)
          (hC_pos hD).le (hf_growth hD (n + 1))
          (fun _ _ => ENNReal.toReal_nonneg) (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable)
          hC (fun j y => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j y)
          (fun j y => f_le_vLim_toReal hD hα0 hα1 (n + 1) j y) n i y
      simp only [G]; nlinarith
    obtain ⟨u, hunn, huB0, humin⟩ := exists_inB0_minimizer_1d (hK_nonneg hD n i) hLG hGlip hGtop
    refine ⟨u, hunn, huB0, fun x r hr => ?_⟩
    have h := humin x r hr
    simp only [G, orderCost] at h ⊢
    linarith
  choose û hû_nn hû_g hû_min using h1d
  choose g hg_cont hg_nn hg_lim using hû_g
  refine ⟨û, fun n => ⟨fun i x => hû_nn n i x, ⟨fun m i => g n i m,
    fun m i => hg_cont n i m, fun m i x => hg_nn n i m x, fun i x => hg_lim n i x⟩⟩,
    fun n i x => ⟨hû_nn n i x, ?_⟩⟩
  refine le_antisymm (le_ciInf fun r => hû_min n i x r.1 r.2) ?_
  exact ciInf_le (bddBelow_bellman_rhs hD hα0 (fun _ _ => ENNReal.toReal_nonneg) n i x)
    ⟨û n i x, hû_nn n i x⟩

/-! ### Section 7: Verification and optimality of every `InB0` minimizer (Part 3) -/

lemma meas_of_inB0 {b : Fin L → ℝ → ℝ} (hb : InB0 b) (i : Fin L) : Measurable (b i) := by
  obtain ⟨_, g, hg_cont, _, hg_lim⟩ := hb
  exact measurable_of_tendsto_metrizable (fun m => (hg_cont m i).measurable)
    (tendsto_pi_nhds.mpr fun x => hg_lim i x)

lemma meas_fbSurplus {û : ℕ → Fin L → ℝ → ℝ} (hû : ∀ n, InB0 (û n)) (n : ℕ) (x : ℝ) :
    ∀ t (σ : Fin (t + 1) → Fin L), Measurable (fbSurplus û n x t σ) := by
  intro t
  induction t with
  | zero => intro _; exact measurable_const
  | succ t ih =>
    intro σ
    have hprev := (ih (Fin.init σ)).comp meas_init
    exact (hprev.add ((meas_of_inB0 (hû (n + t)) _).comp hprev)).sub (measurable_pi_apply _)

lemma feedback_adm {û : ℕ → Fin L → ℝ → ℝ} (hû : ∀ n, InB0 (û n)) (n : ℕ) (x : ℝ) :
    Admissible (feedback û n x) :=
  ⟨fun t _ _ => (hû (n + t)).1 _ _,
   fun t σ => (meas_of_inB0 (hû (n + t)) (σ (Fin.last t))).comp (meas_fbSurplus hû n x t σ)⟩

lemma fbSurplus_cons_succ (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) (i : Fin L) (z : ℝ) :
    ∀ t (σ' : Fin (t + 1) → Fin L) (ξ' : Fin t → ℝ),
      fbSurplus û n x (t + 1) (Fin.cons i σ') (Fin.cons z ξ') =
        fbSurplus û (n + 1) (x + û n i x - z) t σ' ξ' := by
  intro t
  induction t with
  | zero =>
    intro σ' ξ'
    simp only [fbSurplus, init_cons_zero, add_zero]
    have hl : (Fin.cons z ξ' : Fin 1 → ℝ) (Fin.last 0) = z := by
      change (Fin.cons z ξ' : Fin 1 → ℝ) 0 = z; simp
    rw [hl]
  | succ t ih =>
    intro σ' ξ'
    change fbSurplus û n x (t + 1) (Fin.init (Fin.cons i σ' : Fin (t + 3) → Fin L))
          (Fin.init (Fin.cons z ξ' : Fin (t + 2) → ℝ)) +
        û (n + (t + 1)) (Fin.init (Fin.cons i σ' : Fin (t + 3) → Fin L) (Fin.last (t + 1)))
          (fbSurplus û n x (t + 1) (Fin.init (Fin.cons i σ' : Fin (t + 3) → Fin L))
            (Fin.init (Fin.cons z ξ' : Fin (t + 2) → ℝ))) -
        (Fin.cons z ξ' : Fin (t + 2) → ℝ) (Fin.last (t + 1)) =
      fbSurplus û (n + 1) (x + û n i x - z) t (Fin.init σ') (Fin.init ξ') +
        û ((n + 1) + t) (Fin.init σ' (Fin.last t))
          (fbSurplus û (n + 1) (x + û n i x - z) t (Fin.init σ') (Fin.init ξ')) -
        ξ' (Fin.last t)
    rw [init_cons, init_cons]
    have hl1 : (Fin.cons i (Fin.init σ') : Fin (t + 2) → Fin L) (Fin.last (t + 1)) =
        Fin.init σ' (Fin.last t) := by rw [← Fin.succ_last, Fin.cons_succ]
    have hl2 : (Fin.cons z ξ' : Fin (t + 2) → ℝ) (Fin.last (t + 1)) = ξ' (Fin.last t) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    have hnt : n + (t + 1) = (n + 1) + t := by omega
    rw [hl1, hl2, hnt, ih]

lemma shiftPolicy_feedback (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) (i : Fin L) (z : ℝ) :
    shiftPolicy (feedback û n x) i z = feedback û (n + 1) (x + û n i x - z) := by
  funext t σ' ξ'
  simp only [shiftPolicy, feedback]
  have hnt : n + (t + 1) = (n + 1) + t := by omega
  have hl : (Fin.cons i σ' : Fin (t + 2) → Fin L) (Fin.last (t + 1)) = σ' (Fin.last t) := by
    rw [← Fin.succ_last, Fin.cons_succ]
  rw [hnt, hl, fbSurplus_cons_succ]

lemma Jtrunc_feedback_le_vLim {D : Model L} (hD : Standing D) (h42 : Cond42 D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {û : ℕ → Fin L → ℝ → ℝ} (hû : ∀ n, InB0 (û n))
    (hAtt : AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û) :
    ∀ k n i x, Jtrunc D α n k i x (feedback û n x) ≤ vLim D α n i x := by
  set v := fun n i x => (vLim D α n i x).toReal
  have hBell := vLim_bellman hD h42 hα0 hα1
  have hC := (growthC_pos hD hα0 hα1).le
  intro k
  induction k with
  | zero =>
    intro n i x
    rw [Jtrunc_zero]; exact bot_le
  | succ k ih =>
    intro n i x
    rw [Jtrunc_cons hD hα0.le n k i x (feedback û n x) (feedback_adm hû n x)]
    have hu0 : feedback û n x 0 (fun _ => i) Fin.elim0 = û n i x := by
      simp [feedback, fbSurplus]
    simp_rw [hu0, shiftPolicy_feedback]
    have hFv : ENNReal.ofReal (Fnext D n (v (n + 1)) i (x + û n i x)) =
        ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vLim D α (n + 1) j (x + û n i x - z) := by
      rw [Fnext_eq_lintegral hD (fun _ _ => ENNReal.toReal_nonneg)
        (fun j => (vLim_ucont hD hα0 hα1 (n + 1) j).continuous.measurable) hC
        (fun j y => vLim_toReal_le_growth hD hα0 hα1 (n + 1) j y)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; refine lintegral_congr fun z => ?_
      rw [ENNReal.ofReal_toReal (vLim_ne_top hD hα0 hα1 (n + 1) j (x + û n i x - z))]
    have hv_eq : v n i x = orderCost D n i (û n i x) + D.f n i x +
        α * Fnext D n (v (n + 1)) i (x + û n i x) := by
      have hb := hBell n i x
      have ha := (hAtt n i x).2
      linarith
    calc ENNReal.ofReal (orderCost D n i (û n i x) + D.f n i x) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
              Jtrunc D α (n + 1) k j (x + û n i x - z) (feedback û (n + 1) (x + û n i x - z))
        ≤ ENNReal.ofReal (orderCost D n i (û n i x) + D.f n i x) +
          ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * vLim D α (n + 1) j (x + û n i x - z) := by
          gcongr with j _ z
          exact ih (n + 1) j (x + û n i x - z)
      _ = ENNReal.ofReal (orderCost D n i (û n i x) + D.f n i x) +
          ENNReal.ofReal α * ENNReal.ofReal (Fnext D n (v (n + 1)) i (x + û n i x)) := by
          rw [hFv]
      _ = ENNReal.ofReal (orderCost D n i (û n i x) + D.f n i x +
            α * Fnext D n (v (n + 1)) i (x + û n i x)) := by
          rw [← ENNReal.ofReal_mul hα0.le,
            ← ENNReal.ofReal_add (add_nonneg (orderCost_nonneg hD (hAtt n i x).1) (hf_nonneg hD n i x))
              (mul_nonneg hα0.le (Fnext_nonneg hD (fun _ _ => ENNReal.toReal_nonneg) n i _))]
      _ = ENNReal.ofReal (v n i x) := by rw [← hv_eq]
      _ = vLim D α n i x := ENNReal.ofReal_toReal (vLim_ne_top hD hα0 hα1 n i x)

lemma vLim_le_value (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) :
    vLim D α n i x ≤ value D α n i x :=
  iSup_le fun k => le_iInf₂ fun U hU => (iInf₂_le U hU).trans (le_iSup (fun m => Jtrunc D α n m i x U) k)

end SethiChengSS.Infinite.Thm610

open SethiChengSS.Infinite SethiChengSS.Infinite.Thm610

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h42 : Cond42 D)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n, InC1 (fun i x => (vLim D α n i x).toReal)) ∧
    (∃ û : ℕ → Fin L → ℝ → ℝ, (∀ n, InB0 (û n)) ∧
      AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û) ∧
    ∀ û : ℕ → Fin L → ℝ → ℝ, (∀ n, InB0 (û n)) →
      AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û →
      ∀ n i x, Admissible (feedback û n x) ∧ value D α n i x = vLim D α n i x ∧
        Jinf D α n i x (feedback û n x) = value D α n i x := by
  refine ⟨fun n => vLim_inC1 hD hα0 hα1 n, exists_inB0_attains hD h42 hα0 hα1, ?_⟩
  intro û hû hAtt n i x
  have hadm : Admissible (feedback û n x) := feedback_adm hû n x
  have h1 : vLim D α n i x ≤ value D α n i x := vLim_le_value D α n i x
  have h2 : value D α n i x ≤ Jinf D α n i x (feedback û n x) := iInf₂_le (feedback û n x) hadm
  have h3 : Jinf D α n i x (feedback û n x) ≤ vLim D α n i x :=
    iSup_le fun k => Jtrunc_feedback_le_vLim hD h42 hα0 hα1 hû hAtt k n i x
  exact ⟨hadm, le_antisymm (h2.trans h3) h1, le_antisymm (h3.trans h1) h2⟩
