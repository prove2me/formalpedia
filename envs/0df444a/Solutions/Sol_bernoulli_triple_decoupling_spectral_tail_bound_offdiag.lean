-- Prove2me | solution 1 for bernoulli_triple_decoupling_spectral_tail_bound_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T15:55:51.326707+00:00
-- url     : https://prove2.me/submissions/e35d5505-7bc8-44e7-b4fa-389e9e8d8264

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli_measure
import Theorems.Thm_dlp_triple_perfiber_sigma_survival_mixed
import Theorems.Thm_dlp_pair_perfiber_sigma_survival_mixed
import Theorems.Thm_dlp_eq7_pair_integration
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 4000000

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 forward decoupling, k=3.
Closing 55f0c9c3 (bernoulli_triple_decoupling_spectral_tail_bound_offdiag), survival form.

ARCHITECTURE.
  * `namespace Order2` = the COMPLETE, self-contained Proved order-2 (pair) forward bound
    (= the body of the Proved node 9aaf089d, Sol_9aaf089d_close.lean), giving
    `Order2.dlp_forward_tail : P_Ω(s<‖Goff(Ω,Ω)‖) ≤ 978·P_pair(s/12<‖Goff(Ω₁,Ω₂)‖)`.
    This is the de la Peña INDUCTIVE HYPOTHESIS (orders 2..k-1) used to decouple the
    "not all l equal" corners (dlp.txt §4 lines 560-609).
  * `namespace Prove55` = the order-3 layer.  Mirrors the pair close one order up for the
    Tn3 / σ-randomization / eq-7 pieces, and uses `Order2.dlp_forward_tail` FIBERWISE for
    the genuine de la Peña order-induction on the not-all-distinct corners.

de la Peña §4 chain (k=3):
  P_Ω(s<‖Goff3(Ω,Ω,Ω)‖)
    ≤ 3·P_pair(2s/3 < ‖Goff3(Ω₁,Ω₁,Ω₁)+Goff3(Ω₂,Ω₂,Ω₂)‖)         [Lemma 1, 3-copy]
  two-corner = Tn3 − (not-all-equal corners)                       [eq 5; Tn3=8-corner sum]
  ‖Tn3‖ tail  ≤ 2916·P_pair(decoupled 2-copy)                      [eq 7, survival ≥1/2916]
  not-all-equal corners  →  order-2 pair decoupling (Order2.dlp_forward_tail)  [INDUCTION].
-/

namespace Order2

abbrev Pt (n1 n2 : ℕ) := Finset (Fin n1 × Fin n2)

-- ===========================================================================
-- (0) ELEMENTARY: weights nonneg, weights sum to one (finite Bernoulli measure)
-- ===========================================================================
theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ω : Pt n1 n2) : 0 ≤ bernoulliObservationWeight p Ω := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) :
    ∑ Ω : Pt n1 n2, bernoulliObservationWeight p Ω = 1 := by
  unfold bernoulliObservationWeight
  rw [Fintype.sum_pow_mul_eq_add_pow (Fin n1 × Fin n2) p (1 - p)]
  simp

-- ===========================================================================
-- (1) COMPLEMENT BRIDGES: event prob + complement prob = 1 (single and pair)
-- ===========================================================================
theorem event_prob_add_compl {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Prop) :
    bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
  apply Finset.sum_congr rfl
  intro Ω _
  by_cases h : E Ω <;> simp [h]

theorem pair_event_prob_add_compl {n1 n2 : ℕ} (p : ℝ)
    (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p E + bernoulliPairEventProb p (fun Ω₁ Ω₂ => ¬ E Ω₁ Ω₂) = 1 := by
  unfold bernoulliPairEventProb
  have hone : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
      bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂) = 1 := by
    rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
    apply Finset.sum_congr rfl; intro Ω₁ _
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  conv_rhs => rw [← hone]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₂ _
  by_cases h : E Ω₁ Ω₂ <;>
    simp only [h, not_true, not_false_iff, if_true, if_false, mul_one, mul_zero, add_zero, zero_add]

-- ===========================================================================
-- (2) SWAP TOOLKIT (de la Peña σ-selection on the finite powerset; from Sol_9159bae0)
-- swapL/swapR eps (Ω₁,Ω₂) = the σ-selected copies Z^(1)_σ, Z^(2)_σ with eps = {σ=+1}.
-- ===========================================================================
def swapL {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.1 \ epsᶜ) ∪ (q.2 ∩ epsᶜ)
def swapR {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.2 \ epsᶜ) ∪ (q.1 ∩ epsᶜ)

theorem swap_invol {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) :
    (swapL eps (swapL eps q, swapR eps q), swapR eps (swapL eps q, swapR eps q)) = q := by
  have hL : swapL eps (swapL eps q, swapR eps q) = q.1 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  have hR : swapR eps (swapL eps q, swapR eps q) = q.2 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  rw [Prod.ext_iff]; exact ⟨hL, hR⟩

theorem wprod {n1 n2 : ℕ} (p : ℝ) (eps Ω Ω' : Pt n1 n2) :
    bernoulliObservationWeight p ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)) *
        bernoulliObservationWeight p ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ))
      = bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' := by
  have d1 : Disjoint (Ω \ epsᶜ) (Ω' ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have d2 : Disjoint (Ω' \ epsᶜ) (Ω ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have e1 : (Ω \ epsᶜ).card + (Ω ∩ epsᶜ).card = Ω.card :=
    Finset.card_sdiff_add_card_inter Ω epsᶜ
  have e2 : (Ω' \ epsᶜ).card + (Ω' ∩ epsᶜ).card = Ω'.card :=
    Finset.card_sdiff_add_card_inter Ω' epsᶜ
  have hcard : ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card + ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card
      = Ω.card + Ω'.card := by
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2]; omega
  unfold bernoulliObservationWeight
  set N := Fintype.card (Fin n1 × Fin n2) with hN
  set a := ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card with ha
  set b := ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card with hb
  have hcΩ : Ω.card ≤ N := Finset.card_le_univ _
  have hcΩ' : Ω'.card ≤ N := Finset.card_le_univ _
  have hca : a ≤ N := ha ▸ Finset.card_le_univ _
  have hcb : b ≤ N := hb ▸ Finset.card_le_univ _
  rw [show p ^ a * (1-p) ^ (N - a) * (p ^ b * (1-p) ^ (N - b))
        = p ^ (a + b) * (1-p) ^ ((N - a) + (N - b)) from by rw [pow_add, pow_add]; ring,
    show p ^ Ω.card * (1-p) ^ (N - Ω.card) * (p ^ Ω'.card * (1-p) ^ (N - Ω'.card))
        = p ^ (Ω.card + Ω'.card) * (1-p) ^ ((N - Ω.card) + (N - Ω'.card)) from by
          rw [pow_add, pow_add]; ring]
  rw [hcard]; congr 2; omega

-- generic pair-event relabel under the swap (the EQUIDISTRIBUTION identity).
theorem pair_swap_relabel {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2)
    (event : Pt n1 n2 → Pt n1 n2 → Prop) :
    (∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
        bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
          (if event (swapL eps (Ω, Ω')) (swapR eps (Ω, Ω')) then (1:ℝ) else 0))
      = ∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            (if event Ω Ω' then (1:ℝ) else 0) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_nbij' (fun z => (swapL eps z, swapR eps z)) (fun z => (swapL eps z, swapR eps z))
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact swap_invol eps z
  · intro z _; exact swap_invol eps z
  · intro z _
    simp only []
    have hw : bernoulliObservationWeight p (swapL eps z) * bernoulliObservationWeight p (swapR eps z)
        = bernoulliObservationWeight p z.1 * bernoulliObservationWeight p z.2 := by
      simp only [swapL, swapR]; exact wprod p eps z.1 z.2
    rw [hw]

-- ===========================================================================
-- (3) STEP-3 BRIDGE: swapL/swapR select the σ-fiber copies at the indicator level,
-- and their cross product is a degree-≤2 rademacherSign chaos (= Tn2 + mixed chaos).
-- ===========================================================================
theorem cI_swapL {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w.1 w.2
      = if w ∈ eps then centeredIndicator Ω₁ p w.1 w.2 else centeredIndicator Ω₂ p w.1 w.2 := by
  unfold centeredIndicator swapL
  have h : (w.1, w.2) = w := rfl; rw [h]
  by_cases he : w ∈ eps <;> by_cases h1 : w ∈ Ω₁ <;> by_cases h2 : w ∈ Ω₂ <;>
    simp [he, h1, h2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]

theorem cI_swapR {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w : Fin n1 × Fin n2) :
    centeredIndicator (swapR eps (Ω₁, Ω₂)) p w.1 w.2
      = if w ∈ eps then centeredIndicator Ω₂ p w.1 w.2 else centeredIndicator Ω₁ p w.1 w.2 := by
  unfold centeredIndicator swapR
  have h : (w.1, w.2) = w := rfl; rw [h]
  by_cases he : w ∈ eps <;> by_cases h1 : w ∈ Ω₁ <;> by_cases h2 : w ∈ Ω₂ <;>
    simp [he, h1, h2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]

-- the cross-product mixed split (verified: const + linear σ - linear σ - bilinear σσ).
theorem cross_product_mixed {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w1 w2 : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
        * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2
      = (1/4) * (centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
        + (1/4) * rademacherSign eps w1.1 w1.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
        - (1/4) * rademacherSign eps w2.1 w2.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
        - (1/4) * rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2) := by
  rw [cI_swapL, cI_swapR]
  unfold rademacherSign
  have h1 : (w1.1, w1.2) = w1 := rfl
  have h2 : (w2.1, w2.2) = w2 := rfl
  rw [h1, h2]
  set A1 := centeredIndicator Ω₁ p w1.1 w1.2
  set B1 := centeredIndicator Ω₂ p w1.1 w1.2
  set A2 := centeredIndicator Ω₁ p w2.1 w2.2
  set B2 := centeredIndicator Ω₂ p w2.1 w2.2
  by_cases he1 : w1 ∈ eps <;> by_cases he2 : w2 ∈ eps <;>
    simp only [he1, he2, if_true, if_false] <;> ring

-- ===========================================================================
-- (4) THE KEY MATRIX IDENTITY: 4 • G(swapL, swapR) = Tn2C + mixedChaos,
-- where G uses the off-diag representation with coefficient family `a`.
-- This is the de la Peña eq-4 σ-randomization at the matrix/spectralNorm level.
-- ===========================================================================

-- the off-diagonal decoupled statistic built from `a` (matches 9aaf089d's G).
noncomputable def Goff {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
    (if w1 = w2 then (0 : RealMatrix n1 n2)
     else (centeredIndicator Ω₁ p w1.1 w1.2 * centeredIndicator Ω₂ p w2.1 w2.2) • a w1 w2)

-- the four-corner Tn2 statistic = sum of the four corners (Goff at (Ωi,Ωj)).
noncomputable def Tn2 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) : RealMatrix n1 n2 :=
  Goff a p Ω₁ Ω₁ + Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁ + Goff a p Ω₂ Ω₂

-- the linear coefficient (b) and bilinear coefficient (a') of the mixed σ-chaos.
noncomputable def bCoef {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
      else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2))
  - (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
      else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w))

noncomputable def aCoef {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w1 w2 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  (- ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
       * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2

-- Tn2 = the four-corner sum, written as a single off-diagonal double sum with the
-- (A1+B1)(A2+B2) const coefficient (= sum of the four corner coefficients).
theorem Tn2_eq_const_sum {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    Tn2 a p Ω₁ Ω₂ = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 then (0:RealMatrix n1 n2)
       else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
             * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w1 w2) := by
  unfold Tn2 Goff
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- THE KEY MATRIX IDENTITY (de la Peña eq-4 σ-randomization at the matrix level):
-- 4 • Goff(swapL eps (Ω₁,Ω₂), swapR eps (Ω₁,Ω₂))
--   = Tn2 a p Ω₁ Ω₂ + Σ_w σ_w • bCoef w + Σ_{w1≠w2} σ_{w1}σ_{w2} • aCoef w1 w2.

-- LHS = canonical sum of 4*crossproduct (push 4• inside, smul_smul termwise)
theorem four_Goff_LHS_eq_canon {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (4 : ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (4 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
                 * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2)) • a w1 w2) := by
  unfold Goff
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w1 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- The canonical sum splits into 4 double sums via cross_product_mixed.
theorem four_Goff_canon_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : RealMatrix n1 n2)
         else (4 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
               * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2)) • a w1 w2))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0:RealMatrix n1 n2)
           else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [cross_product_mixed]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- Term1 (σ_{w1} linear) = ∑_w σ_w • (first bCoef sum)
theorem four_Goff_Term1_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2))
      = ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2)) := by
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w = w2
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- Term2 (σ_{w2} linear) = - ∑_w σ_w • (second bCoef sum)
theorem four_Goff_Term2_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
      = - ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w)) := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  by_cases h : w1 = w
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul, ← neg_smul]

-- Term3 (bilinear) = the bilinear RHS via aCoef
theorem four_Goff_Term3_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2)) := by
  apply Finset.sum_congr rfl; intro w1 _
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    unfold aCoef
    rw [smul_smul]
    congr 1
    ring

-- ∑_w σ_w • bCoef w = (first sum) + (- second sum), splitting bCoef via smul_sub
theorem four_Goff_linear_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
      = (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2)))
        + (- ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w))) := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w _
  unfold bCoef
  rw [smul_sub]
  abel

theorem four_Goff_swap_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (4 : ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))
      = Tn2 a p Ω₁ Ω₂
        + (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2)) := by
  rw [four_Goff_LHS_eq_canon, four_Goff_canon_split]
  rw [← Tn2_eq_const_sum]
  rw [four_Goff_Term1_eq, four_Goff_Term2_eq, four_Goff_Term3_eq]
  rw [four_Goff_linear_eq]
  abel

-- ===========================================================================
-- (5) PER-FIBER SURVIVAL ON THE SWAP: ‖Tn2‖ ≤ ‖4•Goff(swapL,swapR)‖ on ≥1/324 of σ.
-- Composes the survival child (db8a020b) with the matrix identity (4).
-- ===========================================================================
theorem survival_on_swap {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    rademacherExpectation (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂)
          ≤ spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0) ≥ 1 / 324 := by
  have hsurv := dlp_pair_perfiber_sigma_survival_mixed
    (bCoef a p Ω₁ Ω₂) (aCoef a p Ω₁ Ω₂) (Tn2 a p Ω₁ Ω₂)
  -- rewrite the survival object via the matrix identity (4)
  have hrw : ∀ eps : Pt n1 n2,
      (Tn2 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2))))
        = (4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)) := by
    intro eps; rw [four_Goff_swap_eq]; abel
  -- transport the survival expectation along hrw
  have : (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂)
          ≤ spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0)
    = (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂) ≤ spectralNorm (Tn2 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2))))
      then (1:ℝ) else 0) := by
    funext eps; rw [hrw eps]
  rw [this]; exact hsurv

-- ===========================================================================
-- (6) THE eq-7 INTERCHANGE (Tn2 four-corner side, FULLY PROVED from the bricks):
--   (1/324)·P_pair(t ≤ ‖Tn2 Ω₁ Ω₂‖) ≤ P_pair(t ≤ ‖4·Goff(Ω₁,Ω₂)‖).
-- Composes survival_on_swap + eq-7 combinator (d618ebb8) + pair_swap_relabel (equidist).
-- ===========================================================================
-- ===========================================================================
-- (6) THE eq-7 INTERCHANGE.
-- GENERIC form (norms opaque ⇒ no whnf storm in the Fubini), then a concrete wrapper.
-- Composes survival_on_swap + eq-7 combinator (d618ebb8) + pair_swap_relabel (equidist).
-- ===========================================================================
theorem eq7_interchange_generic {n1 n2 : ℕ}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (Tnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (Snorm : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → ℝ)
    (Dnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (hsurv : ∀ Ω₁ Ω₂ : Pt n1 n2,
      rademacherExpectation (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) ≥ 1/324)
    (hrelabel : ∀ eps : Pt n1 n2,
      (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = ∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0))
    (hrefine : ∀ Ω₁ Ω₂ eps : Pt n1 n2,
      t < Tnorm Ω₁ Ω₂ → Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ → t < Snorm eps Ω₁ Ω₂) :
    (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
  have hstep1 : (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
    apply dlp_eq7_pair_integration p hp0 hp1 (1/324) (by norm_num)
    · intro Ω₁ Ω₂
      unfold rademacherExpectation rademacherObservationWeight
      apply Finset.sum_nonneg; intro eps _
      apply mul_nonneg (by positivity); dsimp only; split <;> norm_num
    · intro Ω₁ Ω₂ hgood
      have hmono : rademacherExpectation
            (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)
          ≤ rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_le_sum; intro eps _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only
        by_cases hT : Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂
        · rw [if_pos hT, if_pos (hrefine Ω₁ Ω₂ eps hgood hT)]
        · rw [if_neg hT]; split <;> norm_num
      exact le_trans (hsurv Ω₁ Ω₂) hmono
  have hstep2 : bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
    unfold bernoulliPairExpectation bernoulliPairEventProb rademacherExpectation
    have hpush : ∀ Ω₁ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
            (∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
          = ∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro Ω₁ Ω₂; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro eps _; ring
    simp only [hpush]
    rw [Finset.sum_congr rfl (fun Ω₁ _ => Finset.sum_comm (γ := Pt n1 n2)
      (f := fun Ω₂ eps => rademacherObservationWeight eps *
        (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))))]
    rw [Finset.sum_comm (γ := Pt n1 n2)]
    have hslice : ∀ eps : Pt n1 n2,
        (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
          rademacherObservationWeight eps *
            (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro eps
      have hfac : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
            rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω₁ _; rw [Finset.mul_sum]
      rw [hfac, hrelabel eps]
    rw [Finset.sum_congr rfl (fun eps _ => hslice eps)]
    rw [← Finset.sum_mul]
    have hradsum : ∑ eps : Pt n1 n2, rademacherObservationWeight eps = 1 := by
      unfold rademacherObservationWeight
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_pow]
      norm_num
    rw [hradsum, one_mul]
  rw [← hstep2]; exact hstep1

-- concrete instantiation: the Tn2-side interchange for our matrix statistics.
theorem eq7_interchange {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn2 a p Ω₁ Ω₂))
      ≤ bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => t < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂)) := by
  refine eq7_interchange_generic p hp0 hp1 t
    (fun Ω₁ Ω₂ => spectralNorm (Tn2 a p Ω₁ Ω₂))
    (fun eps Ω₁ Ω₂ => spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))))
    (fun Ω₁ Ω₂ => spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))
    (fun Ω₁ Ω₂ => survival_on_swap a p Ω₁ Ω₂)
    ?_
    (fun Ω₁ Ω₂ eps h1 h2 => lt_of_lt_of_le h1 h2)
  -- hrelabel: pair_swap_relabel with event = (t < ‖4•Goff‖); Snorm = Dnorm∘swap by rfl.
  intro eps
  exact pair_swap_relabel p eps (fun Ω₁ Ω₂ => t < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))

-- spectralNorm is 1-homogeneous: ‖c • X‖ = |c|·‖X‖.
theorem spectralNorm_smul {n1 n2 : ℕ} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul]; simp [Real.norm_eq_abs]

-- spectralNorm triangle inequality.
theorem spectralNorm_tri {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm; rw [map_add, map_add]; exact norm_add_le _ _

-- spectralNorm sub-triangle inequality.
theorem spectralNorm_sub_tri {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    spectralNorm (X - Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm; rw [map_sub, map_sub]; exact norm_sub_le _ _

-- monotonicity of bernoulliPairEventProb in the event (under nonneg weights).
theorem pair_event_prob_mono {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : Pt n1 n2 → Pt n1 n2 → Prop) (hEF : ∀ Ω₁ Ω₂, E Ω₁ Ω₂ → F Ω₁ Ω₂) :
    bernoulliPairEventProb p E ≤ bernoulliPairEventProb p F := by
  unfold bernoulliPairEventProb
  apply Finset.sum_le_sum; intro Ω₁ _
  apply Finset.sum_le_sum; intro Ω₂ _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg hp0 hp1 _) (weight_nonneg hp0 hp1 _))
  by_cases h : E Ω₁ Ω₂
  · rw [if_pos h, if_pos (hEF Ω₁ Ω₂ h)]
  · rw [if_neg h]; split <;> norm_num

-- union bound on pair event prob: E → F ∨ G pointwise ⇒ P(E) ≤ P(F)+P(G).
theorem pair_union_bound {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F G : Pt n1 n2 → Pt n1 n2 → Prop) (hEFG : ∀ Ω₁ Ω₂, E Ω₁ Ω₂ → F Ω₁ Ω₂ ∨ G Ω₁ Ω₂) :
    bernoulliPairEventProb p E ≤ bernoulliPairEventProb p F + bernoulliPairEventProb p G := by
  unfold bernoulliPairEventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₂ _
  have hw : 0 ≤ bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ :=
    mul_nonneg (weight_nonneg hp0 hp1 _) (weight_nonneg hp0 hp1 _)
  by_cases hE : E Ω₁ Ω₂
  · rcases hEFG Ω₁ Ω₂ hE with hF | hG
    · rw [if_pos hE, if_pos hF]
      have : (0:ℝ) ≤ (if G Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
      nlinarith [hw]
    · rw [if_pos hE, if_pos hG]
      have : (0:ℝ) ≤ (if F Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
      nlinarith [hw]
  · rw [if_neg hE]
    have h1 : (0:ℝ) ≤ (if F Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
    have h2 : (0:ℝ) ≤ (if G Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
    nlinarith [hw]

-- swap Ω₁↔Ω₂ in a pair event prob (the i.i.d. exchangeability, via Finset.sum_comm).
theorem pair_swap_args {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => E Ω₂ Ω₁) = bernoulliPairEventProb p E := by
  unfold bernoulliPairEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
  ring_nf

-- ===========================================================================
-- (6b) de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) LEMMA 1, 3-copy
-- symmetrization, spectralNorm-native on the finite Bernoulli powerset model:
--   P_Ω(s < ‖X Ω‖) ≤ 3·P_pair(2s/3 < ‖X Ω₁ + X Ω₂‖)   for ANY per-block X.
-- ===========================================================================
namespace L1Diag

theorem spectralNorm_two_smul {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    spectralNorm ((2:ℝ) • X) = 2 * spectralNorm X := by
  rw [spectralNorm_smul]; norm_num

theorem single_eq_triple {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Prop) :
    bernoulliEventProb p (fun Ω => E Ω)
      = bernoulliTripleEventProb p (fun Ω _ _ => E Ω) := by
  classical
  unfold bernoulliEventProb bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  have h3 : ∀ Ω2 : Pt n1 n2,
      (∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3 * (if E Ω1 then 1 else 0))
        = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
            (if E Ω1 then 1 else 0) := by
    intro Ω2
    rw [← Finset.sum_mul]
    have : ∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3
        = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 := by
      rw [← Finset.mul_sum, weights_sum_one, mul_one]
    rw [this]
  rw [Finset.sum_congr rfl (fun Ω2 _ => h3 Ω2)]
  have : ∑ Ω2 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        (if E Ω1 then 1 else 0)
      = bernoulliObservationWeight p Ω1 * (if E Ω1 then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun Ω2 _ => by ring :
      ∀ Ω2 ∈ (Finset.univ : Finset (Pt n1 n2)),
        bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          (if E Ω1 then 1 else 0)
        = bernoulliObservationWeight p Ω2 *
          (bernoulliObservationWeight p Ω1 * (if E Ω1 then 1 else 0)))]
    rw [← Finset.sum_mul, weights_sum_one, one_mul]
  rw [this]
  by_cases h : E Ω1 <;> simp [h]

theorem pair_eq_triple {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p (fun Ω1 Ω2 => E Ω1 Ω2)
      = bernoulliTripleEventProb p (fun Ω1 Ω2 _ => E Ω1 Ω2) := by
  classical
  unfold bernoulliPairEventProb bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  apply Finset.sum_congr rfl; intro Ω2 _
  rw [← Finset.sum_mul]
  have : ∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        bernoulliObservationWeight p Ω3
      = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 := by
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  rw [this]

theorem htri {n1 n2 : ℕ} (X1 X2 X3 : RealMatrix n1 n2) (s : ℝ)
    (hs : s < spectralNorm X1) :
    (2*s/3 < spectralNorm (X1 + X2)) ∨ (2*s/3 < spectralNorm (X1 + X3)) ∨
      (2*s/3 < spectralNorm (X2 + X3)) := by
  have hid : (2:ℝ) • X1 = (X1 + X2) + (X1 + X3) - (X2 + X3) := by rw [two_smul]; abel
  have h2 : 2 * spectralNorm X1 = spectralNorm ((2:ℝ) • X1) := (spectralNorm_two_smul X1).symm
  have htria : spectralNorm ((X1 + X2) + (X1 + X3) - (X2 + X3))
      ≤ spectralNorm (X1 + X2) + spectralNorm (X1 + X3) + spectralNorm (X2 + X3) := by
    have e1 : (X1 + X2) + (X1 + X3) - (X2 + X3)
        = ((X1 + X2) + (X1 + X3)) + (-(1:ℝ)) • (X2 + X3) := by rw [neg_one_smul]; abel
    rw [e1]
    refine le_trans (Order2.spectralNorm_tri _ _) ?_
    have hneg : spectralNorm ((-(1:ℝ)) • (X2 + X3)) = spectralNorm (X2 + X3) := by
      rw [spectralNorm_smul]; norm_num
    rw [hneg]
    have := spectralNorm_tri (X1 + X2) (X1 + X3)
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hsum : spectralNorm (X1 + X2) + spectralNorm (X1 + X3) + spectralNorm (X2 + X3)
      ≤ 2*s := by linarith
  rw [hid] at h2
  have : 2 * spectralNorm X1 ≤ 2*s := le_trans (h2.le.trans htria) hsum
  linarith

theorem indicator_union {P Q1 Q2 Q3 : Prop} [Decidable P] [Decidable Q1]
    [Decidable Q2] [Decidable Q3] (h : P → Q1 ∨ Q2 ∨ Q3) :
    (if P then (1:ℝ) else 0)
      ≤ (if Q1 then 1 else 0) + (if Q2 then 1 else 0) + (if Q3 then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, if_true]
    rcases h hP with hq | hq | hq
    · simp only [hq, if_true]; by_cases Q2 <;> by_cases Q3 <;> simp_all <;> norm_num
    · simp only [hq, if_true]; by_cases Q1 <;> by_cases Q3 <;> simp_all <;> norm_num
    · simp only [hq, if_true]; by_cases Q1 <;> by_cases Q2 <;> simp_all <;> norm_num
  · simp only [hP, if_false]; positivity

theorem triple_union_bound {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun Ω1 _ _ => s < spectralNorm (X Ω1))
      ≤ bernoulliTripleEventProb p (fun Ω1 Ω2 _ => 2*s/3 < spectralNorm (X Ω1 + X Ω2))
        + bernoulliTripleEventProb p (fun Ω1 _ Ω3 => 2*s/3 < spectralNorm (X Ω1 + X Ω3))
        + bernoulliTripleEventProb p (fun _ Ω2 Ω3 => 2*s/3 < spectralNorm (X Ω2 + X Ω3)) := by
  classical
  unfold bernoulliTripleEventProb
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω1 _
  apply Finset.sum_le_sum; intro Ω2 _
  apply Finset.sum_le_sum; intro Ω3 _
  set w := bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
    bernoulliObservationWeight p Ω3 with hw
  have hwnn : 0 ≤ w := by
    rw [hw]
    have h1 := weight_nonneg hp0 hp1 Ω1
    have h2 := weight_nonneg hp0 hp1 Ω2
    have h3 := weight_nonneg hp0 hp1 Ω3
    positivity
  have hind := indicator_union (P := s < spectralNorm (X Ω1))
    (Q1 := 2*s/3 < spectralNorm (X Ω1 + X Ω2))
    (Q2 := 2*s/3 < spectralNorm (X Ω1 + X Ω3))
    (Q3 := 2*s/3 < spectralNorm (X Ω2 + X Ω3))
    (fun h => htri (X Ω1) (X Ω2) (X Ω3) s h)
  have := mul_le_mul_of_nonneg_left hind hwnn
  calc w * (if s < spectralNorm (X Ω1) then (1:ℝ) else 0)
      ≤ w * ((if 2*s/3 < spectralNorm (X Ω1 + X Ω2) then 1 else 0)
            + (if 2*s/3 < spectralNorm (X Ω1 + X Ω3) then 1 else 0)
            + (if 2*s/3 < spectralNorm (X Ω2 + X Ω3) then 1 else 0)) := this
    _ = w * (if 2*s/3 < spectralNorm (X Ω1 + X Ω2) then 1 else 0)
          + w * (if 2*s/3 < spectralNorm (X Ω1 + X Ω3) then 1 else 0)
          + w * (if 2*s/3 < spectralNorm (X Ω2 + X Ω3) then 1 else 0) := by ring

theorem pairProb {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2))
      = bernoulliTripleEventProb p (fun Ω1 Ω2 _ => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) :=
  pair_eq_triple p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2))

theorem E13_eq_pair {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun Ω1 _ Ω3 => 2*s/3 < spectralNorm (X Ω1 + X Ω3))
      = bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) := by
  classical
  rw [pairProb]
  unfold bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω3 _
  apply Finset.sum_congr rfl; intro Ω2 _
  ring

theorem E23_eq_pair {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun _ Ω2 Ω3 => 2*s/3 < spectralNorm (X Ω2 + X Ω3))
      = bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) := by
  classical
  unfold bernoulliTripleEventProb bernoulliPairEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω2 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω3 _
  rw [← Finset.sum_mul]
  have hsum : ∑ Ω1 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        bernoulliObservationWeight p Ω3
      = bernoulliObservationWeight p Ω2 * bernoulliObservationWeight p Ω3 := by
    have : ∀ Ω1 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3
        = bernoulliObservationWeight p Ω1 *
          (bernoulliObservationWeight p Ω2 * bernoulliObservationWeight p Ω3) := fun Ω1 => by ring
    rw [Finset.sum_congr rfl (fun Ω1 _ => this Ω1), ← Finset.sum_mul, weights_sum_one, one_mul]
  rw [hsum]

theorem lemma1_diag_3copy {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (X Ω))
      ≤ 3 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (X Ω₁ + X Ω₂)) := by
  rw [single_eq_triple p (fun Ω => s < spectralNorm (X Ω))]
  refine le_trans (triple_union_bound p hp0 hp1 X s) ?_
  rw [← pairProb p X s, E13_eq_pair p X s, E23_eq_pair p X s]
  exact le_of_eq (by ring)

end L1Diag
-- ===========================================================================
-- (7) THE FAITHFUL de la Peña Lemma 1 / eq-5 (k=2): diagonal → TWO-DIAGONAL-CORNER.
-- THE PRECISE REMAINING RESIDUAL.  de la Peña–Montgomery-Smith 1995 (arXiv:math/
-- 9309211) §4 eqs (4)-(5) p.811: the single-sample diagonal U-statistic Goff(Ω,Ω)
-- desymmetrizes to the TWO-DIAGONAL-CORNER sum Goff(Ω₁,Ω₁)+Goff(Ω₂,Ω₂) (the
-- "X+Y" of the 3-copy triangle Lemma 1), constant 3, threshold 2/3.  This is the
-- spectralNorm-valued 3-copy symmetrization on the powerset model.  It is NOT
-- among the listed children (scalar a49de65e has the wrong norming direction;
-- abstract d1b80fe6 cannot instantiate at V = RealMatrix — no NormedAddCommGroup/
-- MeasurableSpace instance).  The cross-term and Tn2 routing BELOW is sorry-free.
-- ===========================================================================
theorem lemma1_diag_to_two_corner {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂)) := by
  exact L1Diag.lemma1_diag_3copy p hp0 hp1 (fun Ω => Goff a p Ω Ω) s

-- ===========================================================================
-- (8) TWO-CORNER → TARGET routing (FULLY PROVED): the two-diagonal-corner pair
-- tail is bounded by the decoupled Goff(Ω₁,Ω₂) tail, via the triangle splits
-- two-corner = Tn2 − cross, cross = Goff(Ω₁,Ω₂)+Goff(Ω₂,Ω₁), + eq7_interchange.
-- ===========================================================================
theorem two_corner_to_target {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ 326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
  -- two-corner = Tn2 − cross  ⇒  ‖two-corner‖ ≤ ‖Tn2‖ + ‖cross‖, cross = G12+G21.
  -- {2s/3 < ‖two-corner‖} ⊆ {s/3 < ‖Tn2‖} ∪ {s/3 < ‖cross‖}.
  have htc_eq : ∀ Ω₁ Ω₂ : Pt n1 n2,
      Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂
        = Tn2 a p Ω₁ Ω₂ - (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁) := by
    intro Ω₁ Ω₂; unfold Tn2; abel
  -- Step 1: union bound (two-corner) ⊆ (Tn2) ∪ (cross).
  have hstep1 : bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
        + bernoulliPairEventProb p
            (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)) := by
    apply pair_union_bound hp0 hp1
    intro Ω₁ Ω₂ htc
    rw [htc_eq] at htc
    have htri := spectralNorm_sub_tri (Tn2 a p Ω₁ Ω₂) (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)
    -- 2s/3 < ‖Tn2‖ + ‖cross‖ ⇒ s/3 < ‖Tn2‖ ∨ s/3 < ‖cross‖
    by_contra hcon; push_neg at hcon
    exact absurd (lt_of_lt_of_le htc htri) (by linarith [hcon.1, hcon.2])
  -- Step 2: cross = G12+G21 ⊆ (G12) ∪ (G21); union bound + swap.
  have hstep2 : bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁))
      ≤ 2 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    have hub := pair_union_bound hp0 hp1
      (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁))
      (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
      (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₂ Ω₁))
      (by
        intro Ω₁ Ω₂ hc
        have htri := spectralNorm_tri (Goff a p Ω₁ Ω₂) (Goff a p Ω₂ Ω₁)
        by_contra hcon; push_neg at hcon
        exact absurd (lt_of_lt_of_le hc htri) (by linarith [hcon.1, hcon.2]))
    -- the G21 term swaps to the G12 term.
    have hswap : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₂ Ω₁))
        = bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) :=
      pair_swap_args p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
    rw [hswap] at hub; linarith [hub]
  -- Step 3: Tn2 tail → eq7_interchange → 324·P(s/12 < ‖Goff‖).
  have hE7 := eq7_interchange a p hp0 hp1 (s/3)
  have hsmul : ∀ Ω₁ Ω₂ : Pt n1 n2,
      ((s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂)) ↔ ((s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    intro Ω₁ Ω₂; rw [spectralNorm_smul]
    have h4 : |(4:ℝ)| = 4 := by norm_num
    rw [h4]; constructor <;> intro h <;> linarith
  have hEv : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    unfold bernoulliPairEventProb
    apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
    rw [show (if (s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂) then (1:ℝ) else 0)
        = (if (s/12) < spectralNorm (Goff a p Ω₁ Ω₂) then (1:ℝ) else 0) from by
      by_cases h : (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)
      · rw [if_pos h, if_pos ((hsmul Ω₁ Ω₂).mpr h)]
      · rw [if_neg h, if_neg (fun hc => h ((hsmul Ω₁ Ω₂).mp hc))]]
  rw [hEv] at hE7
  have hTn2 : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
      ≤ 324 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    nlinarith [hE7]
  -- the cross branch's s/6 tail ≤ s/12 tail (monotone threshold; uses ‖·‖ ≥ 0
  -- so the s<0 case is fine: s/12 < 0 ≤ ‖Goff‖ always).
  have hmono : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    apply pair_event_prob_mono hp0 hp1
    intro Ω₁ Ω₂ h
    have hsn : (0:ℝ) ≤ spectralNorm (Goff a p Ω₁ Ω₂) := by unfold spectralNorm; exact norm_nonneg _
    rcases lt_or_ge s 0 with hs | hs
    · linarith
    · linarith
  -- combine: ≤ 324·P + 2·P ≤ 326·P (at threshold s/12).
  calc bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
        + bernoulliPairEventProb p
            (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)) := hstep1
    _ ≤ 324 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂))
        + 2 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
        linarith [hTn2, hstep2]
    _ ≤ 326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
        linarith [hmono]

-- ===========================================================================
-- (8b) THE de la Peña FORWARD TAIL BOUND (diagonal ≤ 978·decoupled, threshold /12).
-- Chains the faithful Lemma 1 (residual) + two_corner_to_target (Proved).
-- ===========================================================================
theorem dlp_forward_tail {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 978 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
  have hL1 := lemma1_diag_to_two_corner a p hp0 hp1 s
  have hTC := two_corner_to_target a p hp0 hp1 s
  calc bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂)) := hL1
    _ ≤ 3 * (326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂))) := by
        apply mul_le_mul_of_nonneg_left hTC (by norm_num)
    _ = 978 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by ring

end Order2

namespace Prove55

abbrev Pt (n1 n2 : ℕ) := Finset (Fin n1 × Fin n2)

-- ===========================================================================
-- (0) ELEMENTARY: weights nonneg, weights sum to one (finite Bernoulli measure)
-- ===========================================================================
theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ω : Pt n1 n2) : 0 ≤ bernoulliObservationWeight p Ω := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) :
    ∑ Ω : Pt n1 n2, bernoulliObservationWeight p Ω = 1 := by
  unfold bernoulliObservationWeight
  rw [Fintype.sum_pow_mul_eq_add_pow (Fin n1 × Fin n2) p (1 - p)]
  simp

-- ===========================================================================
-- (1) COMPLEMENT BRIDGES: event prob + complement prob = 1 (single, pair, triple)
-- ===========================================================================
theorem event_prob_add_compl {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Prop) :
    bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
  apply Finset.sum_congr rfl
  intro Ω _
  by_cases h : E Ω <;> simp [h]

theorem pair_event_prob_add_compl {n1 n2 : ℕ} (p : ℝ)
    (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p E + bernoulliPairEventProb p (fun Ω₁ Ω₂ => ¬ E Ω₁ Ω₂) = 1 := by
  unfold bernoulliPairEventProb
  have hone : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
      bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂) = 1 := by
    rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
    apply Finset.sum_congr rfl; intro Ω₁ _
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  conv_rhs => rw [← hone]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₂ _
  by_cases h : E Ω₁ Ω₂ <;>
    simp only [h, not_true, not_false_iff, if_true, if_false, mul_one, mul_zero, add_zero, zero_add]

theorem triple_weights_sum_one {n1 n2 : ℕ} (p : ℝ) :
    (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2, ∑ Ω₃ : Pt n1 n2,
      bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂
        * bernoulliObservationWeight p Ω₃) = 1 := by
  rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
  apply Finset.sum_congr rfl; intro Ω₁ _
  have hinner : ∀ Ω₂ : Pt n1 n2, (∑ Ω₃ : Pt n1 n2,
      bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂
        * bernoulliObservationWeight p Ω₃)
      = bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ := by
    intro Ω₂
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  rw [Finset.sum_congr rfl (fun Ω₂ _ => hinner Ω₂)]
  rw [← Finset.mul_sum, weights_sum_one, mul_one]

theorem triple_event_prob_add_compl {n1 n2 : ℕ} (p : ℝ)
    (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p E
      + bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => ¬ E Ω₁ Ω₂ Ω₃) = 1 := by
  unfold bernoulliTripleEventProb
  conv_rhs => rw [← triple_weights_sum_one (n1 := n1) (n2 := n2) p]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₂ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₃ _
  by_cases h : E Ω₁ Ω₂ Ω₃ <;>
    simp only [h, not_true, not_false_iff, if_true, if_false, mul_one, mul_zero, add_zero, zero_add]

-- ===========================================================================
-- (2) SWAP TOOLKIT (2-copy σ-selection; identical to the pair core, σ stays 2-copy
-- even at order 3).  swapL eps q = the σ-selected copy Z_σ (eps = {σ=+1}).
-- ===========================================================================
def swapL {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.1 \ epsᶜ) ∪ (q.2 ∩ epsᶜ)
def swapR {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.2 \ epsᶜ) ∪ (q.1 ∩ epsᶜ)

theorem swap_invol {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) :
    (swapL eps (swapL eps q, swapR eps q), swapR eps (swapL eps q, swapR eps q)) = q := by
  have hL : swapL eps (swapL eps q, swapR eps q) = q.1 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  have hR : swapR eps (swapL eps q, swapR eps q) = q.2 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  rw [Prod.ext_iff]; exact ⟨hL, hR⟩

theorem wprod {n1 n2 : ℕ} (p : ℝ) (eps Ω Ω' : Pt n1 n2) :
    bernoulliObservationWeight p ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)) *
        bernoulliObservationWeight p ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ))
      = bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' := by
  have d1 : Disjoint (Ω \ epsᶜ) (Ω' ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have d2 : Disjoint (Ω' \ epsᶜ) (Ω ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have e1 : (Ω \ epsᶜ).card + (Ω ∩ epsᶜ).card = Ω.card :=
    Finset.card_sdiff_add_card_inter Ω epsᶜ
  have e2 : (Ω' \ epsᶜ).card + (Ω' ∩ epsᶜ).card = Ω'.card :=
    Finset.card_sdiff_add_card_inter Ω' epsᶜ
  have hcard : ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card + ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card
      = Ω.card + Ω'.card := by
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2]; omega
  unfold bernoulliObservationWeight
  set N := Fintype.card (Fin n1 × Fin n2) with hN
  set a := ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card with ha
  set b := ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card with hb
  have hcΩ : Ω.card ≤ N := Finset.card_le_univ _
  have hcΩ' : Ω'.card ≤ N := Finset.card_le_univ _
  have hca : a ≤ N := ha ▸ Finset.card_le_univ _
  have hcb : b ≤ N := hb ▸ Finset.card_le_univ _
  rw [show p ^ a * (1-p) ^ (N - a) * (p ^ b * (1-p) ^ (N - b))
        = p ^ (a + b) * (1-p) ^ ((N - a) + (N - b)) from by rw [pow_add, pow_add]; ring,
    show p ^ Ω.card * (1-p) ^ (N - Ω.card) * (p ^ Ω'.card * (1-p) ^ (N - Ω'.card))
        = p ^ (Ω.card + Ω'.card) * (1-p) ^ ((N - Ω.card) + (N - Ω'.card)) from by
          rw [pow_add, pow_add]; ring]
  rw [hcard]; congr 2; omega

-- σ-selection at the indicator level: cIsel eps Ω₁ Ω₂ w = cI of swapL.
theorem cI_swapL {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w.1 w.2
      = if w ∈ eps then centeredIndicator Ω₁ p w.1 w.2 else centeredIndicator Ω₂ p w.1 w.2 := by
  unfold centeredIndicator swapL
  have h : (w.1, w.2) = w := rfl; rw [h]
  by_cases he : w ∈ eps <;> by_cases h1 : w ∈ Ω₁ <;> by_cases h2 : w ∈ Ω₂ <;>
    simp [he, h1, h2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]

-- the single-factor σ-randomization split (from the subagent derivation).
theorem cIsel_split {n1 n2 : ℕ} (p : ℝ) (eps Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) :
    (if w ∈ eps then centeredIndicator Ω₁ p w.1 w.2 else centeredIndicator Ω₂ p w.1 w.2)
      = (1/2) * ((centeredIndicator Ω₁ p w.1 w.2 + centeredIndicator Ω₂ p w.1 w.2)
          + rademacherSign eps w.1 w.2
              * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) := by
  unfold rademacherSign
  by_cases he : w ∈ eps <;> simp only [he, if_true, if_false] <;> ring

-- ===========================================================================
-- (3) ORDER-3 STATISTICS: Goff3 (off-diag trilinear), Tn3 (8-corner sum),
-- and the mixed-chaos coefficient families b/a/cc that match the Proved
-- survival brick dlp_triple_perfiber_sigma_survival_mixed (27763bc6).
-- ===========================================================================
noncomputable def Goff3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ Ω₃ : Pt n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
    (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
     else (centeredIndicator Ω₁ p w1.1 w1.2 * centeredIndicator Ω₂ p w2.1 w2.2
            * centeredIndicator Ω₃ p w3.1 w3.2) • a w1 w2 w3)

-- Tn3 = the eight-corner sum (all (j1,j2,j3)∈{1,2}³), = the const-coefficient
-- (A+B)(A+B)(A+B) off-diagonal trilinear statistic.
noncomputable def Tn3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
    (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
     else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
            * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)

-- linear-σ coefficient family (degree 1 in σ): symmetrized over the 3 slots.
noncomputable def bCoef3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  let A : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₁ p u.1 u.2
  let B : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₂ p u.1 u.2
  -- slot 1 carries σ_w:
  (∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w = w2 ∨ w = w3 ∨ w2 = w3 then (0:RealMatrix n1 n2)
       else ((A w - B w) * (A w2 + B w2) * (A w3 + B w3)) • a w w2 w3))
  + (∑ w1 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w ∨ w1 = w3 ∨ w = w3 then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (A w - B w) * (A w3 + B w3)) • a w1 w w3))
  + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w ∨ w2 = w then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (A w2 + B w2) * (A w - B w)) • a w1 w2 w))

-- bilinear-σσ coefficient family (degree 2 in σ): symmetrized over the 3 pairs.
noncomputable def aCoef3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (u v : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  let A : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₁ p u.1 u.2
  let B : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₂ p u.1 u.2
  -- slots (1,2) carry σ_u σ_v:
  (∑ w3 : Fin n1 × Fin n2,
      (if u = v ∨ u = w3 ∨ v = w3 then (0:RealMatrix n1 n2)
       else ((A u - B u) * (A v - B v) * (A w3 + B w3)) • a u v w3))
  + (∑ w2 : Fin n1 × Fin n2,
      (if u = w2 ∨ u = v ∨ w2 = v then (0:RealMatrix n1 n2)
       else ((A u - B u) * (A w2 + B w2) * (A v - B v)) • a u w2 v))
  + (∑ w1 : Fin n1 × Fin n2,
      (if w1 = u ∨ w1 = v ∨ u = v then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (A u - B u) * (A v - B v)) • a w1 u v))

-- trilinear-σσσ coefficient family (degree 3 in σ): the all-distinct triple.
noncomputable def ccCoef3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w1 w2 w3 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  let A : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₁ p u.1 u.2
  let B : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₂ p u.1 u.2
  ((A w1 - B w1) * (A w2 - B w2) * (A w3 - B w3)) • a w1 w2 w3

-- ===========================================================================
-- (4) THE ORDER-3 σ-RANDOMIZATION IDENTITY: 8 • Goff3(swapL,swapL,swapL)
--   = Tn3 + Σσ•bCoef3 + Σσσ•aCoef3 + Σσσσ•ccCoef3.
-- ===========================================================================

-- single-factor: cI of swapL = (1/2)((A+B) + σ_w (A-B)).
theorem cI_swapL_split {n1 n2 : ℕ} (p : ℝ) (eps Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w.1 w.2
      = (1/2) * ((centeredIndicator Ω₁ p w.1 w.2 + centeredIndicator Ω₂ p w.1 w.2)
          + rademacherSign eps w.1 w.2
              * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) := by
  rw [cI_swapL]; exact cIsel_split p eps Ω₁ Ω₂ w

-- LHS canonicalization: push 8• inside the triple sum.
theorem eight_Goff3_LHS_eq_canon {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (8 : ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (8 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
                 * centeredIndicator (swapL eps (Ω₁, Ω₂)) p w2.1 w2.2
                 * centeredIndicator (swapL eps (Ω₁, Ω₂)) p w3.1 w3.2)) • a w1 w2 w3) := by
  unfold Goff3
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w1 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- abbreviations for the centered indicators (sum S and difference D at a slot).
-- canon split: the canonical sum = const + grouped-linear + grouped-double + grouped-triple,
-- where each off-diag coefficient is split via the three cI_swapL_split factors + ring.
theorem eight_Goff3_canon_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else (8 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
               * centeredIndicator (swapL eps (Ω₁, Ω₂)) p w2.1 w2.2
               * centeredIndicator (swapL eps (Ω₁, Ω₂)) p w3.1 w3.2)) • a w1 w2 w3))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w2.1 w2.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
                • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
                • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
                • a w1 w2 w3)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    rw [cI_swapL_split, cI_swapL_split, cI_swapL_split]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring


-- ===========================================================================
-- (3b) σ-RANDOMIZATION COLLECTION: canon blocks → brick shape (T + Σσ•b + Σσσ•a + Σσσσ•cc).
-- ===========================================================================

-- TRILINEAR collection: canon trilinear block = Σ_{distinct} σσσ • ccCoef3.
theorem eight_Goff3_Term_tri {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
              * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
            • a w1 w2 w3))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3) := by
  apply Finset.sum_congr rfl; intro w1 _
  apply Finset.sum_congr rfl; intro w2 _
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    unfold ccCoef3
    rw [smul_smul]

-- helper: the canon bilinear block, split into its 3 σ-pair sub-blocks (sum_add_distrib).
theorem eight_Goff3_bilin_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
            • a w1 w2 w3))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
               * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2) •
               (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                 * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) •
               (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                 * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    simp only [smul_smul]
    rw [← add_smul, ← add_smul]

-- BILINEAR collection: the 3 σ-pair sub-blocks = Σ_{w1≠w2} σσ • aCoef3.
theorem eight_Goff3_Term_bilin {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) •
           (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
             * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
             * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
      + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
               * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
      + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
               * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
            else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
              • aCoef3 a p Ω₁ Ω₂ w1 w2) := by
  symm
  have hsplit :
      (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
          (if u = v then (0 : RealMatrix n1 n2)
            else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2)
              • aCoef3 a p Ω₁ Ω₂ u v))
        = (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
            (if u = v then (0 : RealMatrix n1 n2)
              else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                (∑ w3 : Fin n1 × Fin n2,
                  (if u = v ∨ u = w3 ∨ v = w3 then (0:RealMatrix n1 n2)
                   else ((centeredIndicator Ω₁ p u.1 u.2 - centeredIndicator Ω₂ p u.1 u.2)
                        * (centeredIndicator Ω₁ p v.1 v.2 - centeredIndicator Ω₂ p v.1 v.2)
                        * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a u v w3))))
          + (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
              (if u = v then (0 : RealMatrix n1 n2)
                else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                  (∑ w2 : Fin n1 × Fin n2,
                    (if u = w2 ∨ u = v ∨ w2 = v then (0:RealMatrix n1 n2)
                     else ((centeredIndicator Ω₁ p u.1 u.2 - centeredIndicator Ω₂ p u.1 u.2)
                          * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                          * (centeredIndicator Ω₁ p v.1 v.2 - centeredIndicator Ω₂ p v.1 v.2)) • a u w2 v))))
          + (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
              (if u = v then (0 : RealMatrix n1 n2)
                else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                  (∑ w1 : Fin n1 × Fin n2,
                    (if w1 = u ∨ w1 = v ∨ u = v then (0:RealMatrix n1 n2)
                     else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                          * (centeredIndicator Ω₁ p u.1 u.2 - centeredIndicator Ω₂ p u.1 u.2)
                          * (centeredIndicator Ω₁ p v.1 v.2 - centeredIndicator Ω₂ p v.1 v.2)) • a w1 u v)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    by_cases h : u = v
    · simp [h]
    · rw [if_neg h, if_neg h, if_neg h, if_neg h]
      unfold aCoef3
      simp only
      rw [smul_add, smul_add]
  rw [hsplit]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w2 _
    by_cases h12 : w1 = w2
    · have : ∀ w3 : Fin n1 × Fin n2, (w1 = w2 ∨ w1 = w3 ∨ w2 = w3) := fun w3 => Or.inl h12
      simp only [if_pos h12]
      symm
      rw [Finset.sum_eq_zero]
      intro w3 _; rw [if_pos (this w3)]
    · rw [if_neg h12, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w3 _
      by_cases h : w1 = w3 ∨ w2 = w3
      · rw [if_pos (Or.inr (by tauto)), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]
  · apply Finset.sum_congr rfl; intro w1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    by_cases h13 : w1 = v
    · simp only [if_pos h13]
      symm
      rw [Finset.sum_eq_zero]
      intro w2 _; rw [if_pos (by tauto)]
    · rw [if_neg h13, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w2 _
      by_cases h : w1 = w2 ∨ w2 = v
      · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]
  · symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    by_cases h23 : u = v
    · simp only [if_pos h23]
      symm
      rw [Finset.sum_eq_zero]
      intro w1 _; rw [if_pos (by tauto)]
    · rw [if_neg h23, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w1 _
      by_cases h : w1 = u ∨ w1 = v
      · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]

-- LINEAR collection: canon linear block = Σ_w σ_w • bCoef3.
theorem eight_Goff3_Term_lin {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
            • a w1 w2 w3))
      = ∑ w : Fin n1 × Fin n2,
          rademacherSign eps w.1 w.2 • bCoef3 a p Ω₁ Ω₂ w := by
  symm
  have hsplit :
      (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef3 a p Ω₁ Ω₂ w)
        = (∑ w : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            rademacherSign eps w.1 w.2 •
              (if w = w2 ∨ w = w3 ∨ w2 = w3 then (0:RealMatrix n1 n2)
               else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                    * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                    * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w w2 w3))
          + (∑ w : Fin n1 × Fin n2, ∑ w1 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              rademacherSign eps w.1 w.2 •
                (if w1 = w ∨ w1 = w3 ∨ w = w3 then (0:RealMatrix n1 n2)
                 else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                      * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                      * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w w3))
          + (∑ w : Fin n1 × Fin n2, ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              rademacherSign eps w.1 w.2 •
                (if w1 = w2 ∨ w1 = w ∨ w2 = w then (0:RealMatrix n1 n2)
                 else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                      * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                      * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w2 w)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    unfold bCoef3
    simp only
    rw [smul_add, smul_add]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w2 _; rw [Finset.smul_sum]
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w1 _; rw [Finset.smul_sum]
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w1 _; rw [Finset.smul_sum]
  rw [hsplit]
  have hcanon :
      (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)))
            • a w1 w2 w3))
        = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else rademacherSign eps w1.1 w1.2 •
               (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                 * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else rademacherSign eps w2.1 w2.2 •
                 (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                   * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
                   * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else rademacherSign eps w3.1 w3.2 •
                 (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                   * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                   * (centeredIndicator Ω₁ p w3.1 w3.2 - centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w1 _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w2 _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · simp [h]
    · simp only [h, if_false]
      rw [add_smul, add_smul, smul_smul, smul_smul, smul_smul]
  rw [hcanon]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w2 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]
  · symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w ∨ w1 = w3 ∨ w = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w2 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]

-- Tn3 = the const block of the canon split (definitional).
theorem Tn3_eq_const_block {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    Tn3 a p Ω₁ Ω₂ = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
       else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3) := by
  rfl

-- THE ORDER-3 σ-RANDOMIZATION IDENTITY (de la Peña eq-4, k=3, all-slots l=1):
--   8 • Goff3(swapL,swapL,swapL) = Tn3 + Σσ•bCoef3 + Σ_{w1≠w2}σσ•aCoef3 + Σ_{distinct}σσσ•ccCoef3.
theorem eight_Goff3_swap_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (8 : ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂))
      = Tn3 a p Ω₁ Ω₂
        + (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef3 a p Ω₁ Ω₂ w)
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef3 a p Ω₁ Ω₂ w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3)) := by
  rw [eight_Goff3_LHS_eq_canon, eight_Goff3_canon_split]
  rw [← Tn3_eq_const_block]
  rw [eight_Goff3_bilin_split]
  rw [eight_Goff3_Term_bilin, eight_Goff3_Term_lin, eight_Goff3_Term_tri]

-- ===========================================================================
-- (5) PER-FIBER SURVIVAL ON THE TRIPLE SWAP: ‖Tn3‖ ≤ ‖8•Goff3(swap,swap,swap)‖ on ≥1/2916.
-- Composes the Proved order-3 survival brick (27763bc6) with the matrix identity.
-- ===========================================================================
theorem survival_on_swap3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    rademacherExpectation (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂)
          ≤ spectralNorm ((8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂))
              (swapL eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0) ≥ 1 / 2916 := by
  have hsurv := dlp_triple_perfiber_sigma_survival_mixed
    (bCoef3 a p Ω₁ Ω₂) (aCoef3 a p Ω₁ Ω₂) (ccCoef3 a p Ω₁ Ω₂) (Tn3 a p Ω₁ Ω₂)
  have hrw : ∀ eps : Pt n1 n2,
      (Tn3 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef3 a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                    • aCoef3 a p Ω₁ Ω₂ w1 w2))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3))))
        = (8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂)) := by
    intro eps; rw [eight_Goff3_swap_eq]; abel
  have : (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂)
          ≤ spectralNorm ((8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (swapL eps (Ω₁, Ω₂))
              (swapL eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0)
    = (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂) ≤ spectralNorm (Tn3 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef3 a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                    • aCoef3 a p Ω₁ Ω₂ w1 w2))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3))))
      then (1:ℝ) else 0) := by
    funext eps; rw [hrw eps]
  rw [this]; exact hsurv

-- ===========================================================================
-- (6) THE eq-7 INTERCHANGE (order-3, constant 1/2916).  GENERIC form (opaque norms),
-- then a concrete wrapper.  Composes survival_on_swap3 + eq-7 combinator (d618ebb8) +
-- Order2.pair_swap_relabel (equidistribution).  Mirror of Order2.eq7_interchange_generic.
-- ===========================================================================
theorem eq7_interchange3_generic {n1 n2 : ℕ}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (Tnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (Snorm : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → ℝ)
    (Dnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (hsurv : ∀ Ω₁ Ω₂ : Pt n1 n2,
      rademacherExpectation (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) ≥ 1/2916)
    (hrelabel : ∀ eps : Pt n1 n2,
      (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = ∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0))
    (hrefine : ∀ Ω₁ Ω₂ eps : Pt n1 n2,
      t < Tnorm Ω₁ Ω₂ → Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ → t < Snorm eps Ω₁ Ω₂) :
    (1/2916) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
  have hstep1 : (1/2916) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
    apply dlp_eq7_pair_integration p hp0 hp1 (1/2916) (by norm_num)
    · intro Ω₁ Ω₂
      unfold rademacherExpectation rademacherObservationWeight
      apply Finset.sum_nonneg; intro eps _
      apply mul_nonneg (by positivity); dsimp only; split <;> norm_num
    · intro Ω₁ Ω₂ hgood
      have hmono : rademacherExpectation
            (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)
          ≤ rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_le_sum; intro eps _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only
        by_cases hT : Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂
        · rw [if_pos hT, if_pos (hrefine Ω₁ Ω₂ eps hgood hT)]
        · rw [if_neg hT]; split <;> norm_num
      exact le_trans (hsurv Ω₁ Ω₂) hmono
  have hstep2 : bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
    unfold bernoulliPairExpectation bernoulliPairEventProb rademacherExpectation
    have hpush : ∀ Ω₁ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
            (∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
          = ∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro Ω₁ Ω₂; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro eps _; ring
    simp only [hpush]
    rw [Finset.sum_congr rfl (fun Ω₁ _ => Finset.sum_comm (γ := Pt n1 n2)
      (f := fun Ω₂ eps => rademacherObservationWeight eps *
        (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))))]
    rw [Finset.sum_comm (γ := Pt n1 n2)]
    have hslice : ∀ eps : Pt n1 n2,
        (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
          rademacherObservationWeight eps *
            (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro eps
      have hfac : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
            rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω₁ _; rw [Finset.mul_sum]
      rw [hfac, hrelabel eps]
    rw [Finset.sum_congr rfl (fun eps _ => hslice eps)]
    rw [← Finset.sum_mul]
    have hradsum : ∑ eps : Pt n1 n2, rademacherObservationWeight eps = 1 := by
      unfold rademacherObservationWeight
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_pow]
      norm_num
    rw [hradsum, one_mul]
  rw [← hstep2]; exact hstep1

-- ===========================================================================
-- (M) MIXED (swapL, swapR, swapR) [pattern l=(1,2,2)] σ-RANDOMIZATION CHAIN.
-- swapR flips the σ-difference sign: cI(swapR) = (1/2)((A+B) - σ(A-B)).
-- ===========================================================================

-- single-factor: cI of swapR = (1/2)((A+B) - σ_w (A-B)) = (1/2)((A+B) + σ_w (B-A)).
theorem cI_swapR_split {n1 n2 : ℕ} (p : ℝ) (eps Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) :
    centeredIndicator (Order2.swapR eps (Ω₁, Ω₂)) p w.1 w.2
      = (1/2) * ((centeredIndicator Ω₁ p w.1 w.2 + centeredIndicator Ω₂ p w.1 w.2)
          + rademacherSign eps w.1 w.2
              * (centeredIndicator Ω₂ p w.1 w.2 - centeredIndicator Ω₁ p w.1 w.2)) := by
  rw [Order2.cI_swapR]
  unfold rademacherSign
  by_cases he : w ∈ eps <;> simp only [he, if_true, if_false] <;> ring

-- LHS canonicalization: push 8• inside the triple sum (slots 1=swapL, 2,3=swapR).
theorem eightM_Goff3_LHS_eq_canon {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (8 : ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))
        (Order2.swapR eps (Ω₁, Ω₂))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (8 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
                 * centeredIndicator (Order2.swapR eps (Ω₁, Ω₂)) p w2.1 w2.2
                 * centeredIndicator (Order2.swapR eps (Ω₁, Ω₂)) p w3.1 w3.2)) • a w1 w2 w3) := by
  unfold Goff3
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w1 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- canon split with the (1,2,2) signs:
--   linear:  +σ₁ D₁ S₂ S₃  − σ₂ S₁ D₂ S₃  − σ₃ S₁ S₂ D₃
--   bilinear:−σ₁σ₂ D₁ D₂ S₃ − σ₁σ₃ D₁ S₂ D₃ + σ₂σ₃ S₁ D₂ D₃
--   trilinear:+σ₁σ₂σ₃ D₁ D₂ D₃   (same as all-swapL).
theorem eightM_Goff3_canon_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else (8 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
               * centeredIndicator (Order2.swapR eps (Ω₁, Ω₂)) p w2.1 w2.2
               * centeredIndicator (Order2.swapR eps (Ω₁, Ω₂)) p w3.1 w3.2)) • a w1 w2 w3))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w2.1 w2.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
                • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                  * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
              + rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                  * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2))
              + rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                  * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
                • a w1 w2 w3))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else
              (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2 *
                ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                  * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
                • a w1 w2 w3)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    rw [cI_swapL_split, cI_swapR_split, cI_swapR_split]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- mixed linear-σ coefficient family for pattern (1,2,2):
--   slot 1 carries +(A-B), slots 2,3 carry +(B-A).
noncomputable def bCoefM3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  let A : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₁ p u.1 u.2
  let B : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₂ p u.1 u.2
  (∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w = w2 ∨ w = w3 ∨ w2 = w3 then (0:RealMatrix n1 n2)
       else ((A w - B w) * (A w2 + B w2) * (A w3 + B w3)) • a w w2 w3))
  + (∑ w1 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w ∨ w1 = w3 ∨ w = w3 then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (B w - A w) * (A w3 + B w3)) • a w1 w w3))
  + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w ∨ w2 = w then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (A w2 + B w2) * (B w - A w)) • a w1 w2 w))

-- mixed bilinear-σσ coefficient family for pattern (1,2,2):
--   (1,2): (Au-Bu)(Bv-Av)S₃ ; (1,3): (Au-Bu)S₂(Bv-Av) ; (2,3): S₁(Bu-Au)(Bv-Av).
noncomputable def aCoefM3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (u v : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  let A : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₁ p u.1 u.2
  let B : Fin n1 × Fin n2 → ℝ := fun u => centeredIndicator Ω₂ p u.1 u.2
  (∑ w3 : Fin n1 × Fin n2,
      (if u = v ∨ u = w3 ∨ v = w3 then (0:RealMatrix n1 n2)
       else ((A u - B u) * (B v - A v) * (A w3 + B w3)) • a u v w3))
  + (∑ w2 : Fin n1 × Fin n2,
      (if u = w2 ∨ u = v ∨ w2 = v then (0:RealMatrix n1 n2)
       else ((A u - B u) * (A w2 + B w2) * (B v - A v)) • a u w2 v))
  + (∑ w1 : Fin n1 × Fin n2,
      (if w1 = u ∨ w1 = v ∨ u = v then (0:RealMatrix n1 n2)
       else ((A w1 + B w1) * (B u - A u) * (B v - A v)) • a w1 u v))

-- TRILINEAR collection: canon trilinear block = Σ_{distinct} σσσ • ccCoef3
-- (signs: (A₁-B₁)(B₂-A₂)(B₃-A₃) = (A₁-B₁)(A₂-B₂)(A₃-B₃) = ccCoef3).
theorem eightM_Goff3_Term_tri {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
              * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
              * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
            • a w1 w2 w3))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3) := by
  apply Finset.sum_congr rfl; intro w1 _
  apply Finset.sum_congr rfl; intro w2 _
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    unfold ccCoef3
    rw [smul_smul]
    congr 2
    ring

-- helper: the canon bilinear block, split into its 3 σ-pair sub-blocks (sum_add_distrib).
theorem eightM_Goff3_bilin_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
              * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
            • a w1 w2 w3))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
               * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2) •
               (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                 * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)) • a w1 w2 w3)))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) •
               (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                 * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)) • a w1 w2 w3))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    simp only [smul_smul]
    rw [← add_smul, ← add_smul]

-- BILINEAR collection: the 3 σ-pair sub-blocks = Σ_{w1≠w2} σσ • aCoefM3.
theorem eightM_Goff3_Term_bilin {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) •
           (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
             * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
             * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
      + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w3.1 w3.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
               * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)) • a w1 w2 w3)))
      + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w2.1 w2.2 * rademacherSign eps w3.1 w3.2) •
             (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
               * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
               * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)) • a w1 w2 w3)))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
            else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
              • aCoefM3 a p Ω₁ Ω₂ w1 w2) := by
  symm
  have hsplit :
      (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
          (if u = v then (0 : RealMatrix n1 n2)
            else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2)
              • aCoefM3 a p Ω₁ Ω₂ u v))
        = (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
            (if u = v then (0 : RealMatrix n1 n2)
              else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                (∑ w3 : Fin n1 × Fin n2,
                  (if u = v ∨ u = w3 ∨ v = w3 then (0:RealMatrix n1 n2)
                   else ((centeredIndicator Ω₁ p u.1 u.2 - centeredIndicator Ω₂ p u.1 u.2)
                        * (centeredIndicator Ω₂ p v.1 v.2 - centeredIndicator Ω₁ p v.1 v.2)
                        * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a u v w3))))
          + (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
              (if u = v then (0 : RealMatrix n1 n2)
                else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                  (∑ w2 : Fin n1 × Fin n2,
                    (if u = w2 ∨ u = v ∨ w2 = v then (0:RealMatrix n1 n2)
                     else ((centeredIndicator Ω₁ p u.1 u.2 - centeredIndicator Ω₂ p u.1 u.2)
                          * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                          * (centeredIndicator Ω₂ p v.1 v.2 - centeredIndicator Ω₁ p v.1 v.2)) • a u w2 v))))
          + (∑ u : Fin n1 × Fin n2, ∑ v : Fin n1 × Fin n2,
              (if u = v then (0 : RealMatrix n1 n2)
                else (rademacherSign eps u.1 u.2 * rademacherSign eps v.1 v.2) •
                  (∑ w1 : Fin n1 × Fin n2,
                    (if w1 = u ∨ w1 = v ∨ u = v then (0:RealMatrix n1 n2)
                     else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                          * (centeredIndicator Ω₂ p u.1 u.2 - centeredIndicator Ω₁ p u.1 u.2)
                          * (centeredIndicator Ω₂ p v.1 v.2 - centeredIndicator Ω₁ p v.1 v.2)) • a w1 u v)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v _
    by_cases h : u = v
    · simp [h]
    · rw [if_neg h, if_neg h, if_neg h, if_neg h]
      unfold aCoefM3
      simp only
      rw [smul_add, smul_add]
  rw [hsplit]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w2 _
    by_cases h12 : w1 = w2
    · have : ∀ w3 : Fin n1 × Fin n2, (w1 = w2 ∨ w1 = w3 ∨ w2 = w3) := fun w3 => Or.inl h12
      simp only [if_pos h12]
      symm
      rw [Finset.sum_eq_zero]
      intro w3 _; rw [if_pos (this w3)]
    · rw [if_neg h12, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w3 _
      by_cases h : w1 = w3 ∨ w2 = w3
      · rw [if_pos (Or.inr (by tauto)), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]
  · apply Finset.sum_congr rfl; intro w1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    by_cases h13 : w1 = v
    · simp only [if_pos h13]
      symm
      rw [Finset.sum_eq_zero]
      intro w2 _; rw [if_pos (by tauto)]
    · rw [if_neg h13, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w2 _
      by_cases h : w1 = w2 ∨ w2 = v
      · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]
  · symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    by_cases h23 : u = v
    · simp only [if_pos h23]
      symm
      rw [Finset.sum_eq_zero]
      intro w1 _; rw [if_pos (by tauto)]
    · rw [if_neg h23, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro w1 _
      by_cases h : w1 = u ∨ w1 = v
      · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
      · rw [if_neg (by tauto), if_neg (by tauto), smul_smul]

-- LINEAR collection: canon linear block = Σ_w σ_w • bCoefM3.
theorem eightM_Goff3_Term_lin {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
            • a w1 w2 w3))
      = ∑ w : Fin n1 × Fin n2,
          rademacherSign eps w.1 w.2 • bCoefM3 a p Ω₁ Ω₂ w := by
  symm
  have hsplit :
      (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoefM3 a p Ω₁ Ω₂ w)
        = (∑ w : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            rademacherSign eps w.1 w.2 •
              (if w = w2 ∨ w = w3 ∨ w2 = w3 then (0:RealMatrix n1 n2)
               else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                    * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                    * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w w2 w3))
          + (∑ w : Fin n1 × Fin n2, ∑ w1 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              rademacherSign eps w.1 w.2 •
                (if w1 = w ∨ w1 = w3 ∨ w = w3 then (0:RealMatrix n1 n2)
                 else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                      * (centeredIndicator Ω₂ p w.1 w.2 - centeredIndicator Ω₁ p w.1 w.2)
                      * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w w3))
          + (∑ w : Fin n1 × Fin n2, ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              rademacherSign eps w.1 w.2 •
                (if w1 = w2 ∨ w1 = w ∨ w2 = w then (0:RealMatrix n1 n2)
                 else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                      * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                      * (centeredIndicator Ω₂ p w.1 w.2 - centeredIndicator Ω₁ p w.1 w.2)) • a w1 w2 w)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    unfold bCoefM3
    simp only
    rw [smul_add, smul_add]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w2 _; rw [Finset.smul_sum]
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w1 _; rw [Finset.smul_sum]
    · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w1 _; rw [Finset.smul_sum]
  rw [hsplit]
  have hcanon :
      (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
         else
          (rademacherSign eps w1.1 w1.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w2.1 w2.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
              * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2))
          + rademacherSign eps w3.1 w3.2 *
            ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
              * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)))
            • a w1 w2 w3))
        = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else rademacherSign eps w1.1 w1.2 •
               (((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                 * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else rademacherSign eps w2.1 w2.2 •
                 (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                   * (centeredIndicator Ω₂ p w2.1 w2.2 - centeredIndicator Ω₁ p w2.1 w2.2)
                   * (centeredIndicator Ω₁ p w3.1 w3.2 + centeredIndicator Ω₂ p w3.1 w3.2)) • a w1 w2 w3)))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else rademacherSign eps w3.1 w3.2 •
                 (((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                   * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
                   * (centeredIndicator Ω₂ p w3.1 w3.2 - centeredIndicator Ω₁ p w3.1 w3.2)) • a w1 w2 w3))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w1 _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w2 _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · simp [h]
    · simp only [h, if_false]
      rw [add_smul, add_smul, smul_smul, smul_smul, smul_smul]
  rw [hcanon]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w2 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]
  · symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w1 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w ∨ w1 = w3 ∨ w = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w2 _
    apply Finset.sum_congr rfl; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · rw [if_pos (by tauto), if_pos (by tauto), smul_zero]
    · rw [if_neg (by tauto), if_neg (by tauto)]

-- THE ORDER-3 σ-RANDOMIZATION IDENTITY (de la Peña eq-4, k=3, pattern l=(1,2,2)):
--   8 • Goff3(swapL,swapR,swapR) = Tn3 + Σσ•bCoefM3 + Σ_{w1≠w2}σσ•aCoefM3 + Σ_{distinct}σσσ•ccCoef3.
theorem eightM_Goff3_swap_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (8 : ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))
        (Order2.swapR eps (Ω₁, Ω₂))
      = Tn3 a p Ω₁ Ω₂
        + (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoefM3 a p Ω₁ Ω₂ w)
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoefM3 a p Ω₁ Ω₂ w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3)) := by
  rw [eightM_Goff3_LHS_eq_canon, eightM_Goff3_canon_split]
  rw [← Tn3_eq_const_block]
  rw [eightM_Goff3_bilin_split]
  rw [eightM_Goff3_Term_bilin, eightM_Goff3_Term_lin, eightM_Goff3_Term_tri]

-- PER-FIBER SURVIVAL ON THE MIXED (swapL,swapR,swapR) SWAP:
--   ‖Tn3‖ ≤ ‖8•Goff3(swapL,swapR,swapR)‖ on ≥1/2916 of σ.
theorem survivalM_on_swap3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    rademacherExpectation (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂)
          ≤ spectralNorm ((8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))
              (Order2.swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0) ≥ 1 / 2916 := by
  have hsurv := dlp_triple_perfiber_sigma_survival_mixed
    (bCoefM3 a p Ω₁ Ω₂) (aCoefM3 a p Ω₁ Ω₂) (ccCoef3 a p Ω₁ Ω₂) (Tn3 a p Ω₁ Ω₂)
  have hrw : ∀ eps : Pt n1 n2,
      (Tn3 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoefM3 a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                    • aCoefM3 a p Ω₁ Ω₂ w1 w2))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3))))
        = (8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))
            (Order2.swapR eps (Ω₁, Ω₂)) := by
    intro eps; rw [eightM_Goff3_swap_eq]; abel
  have : (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂)
          ≤ spectralNorm ((8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))
              (Order2.swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0)
    = (fun eps =>
      if spectralNorm (Tn3 a p Ω₁ Ω₂) ≤ spectralNorm (Tn3 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoefM3 a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                    • aCoefM3 a p Ω₁ Ω₂ w1 w2))
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • ccCoef3 a p Ω₁ Ω₂ w1 w2 w3))))
      then (1:ℝ) else 0) := by
    funext eps; rw [hrw eps]
  rw [this]; exact hsurv

-- THE eq-7 INTERCHANGE for the MIXED copy-selection l=(1,2,2):
--   (1/2916)·P_pair(t < ‖Tn3 Ω₁ Ω₂‖) ≤ P_pair(t < ‖8•Goff3(Ω₁,Ω₂,Ω₂)‖).
theorem eq7_interchange3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (1/2916) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn3 a p Ω₁ Ω₂))
      ≤ bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => t < spectralNorm ((8:ℝ) • Goff3 a p Ω₁ Ω₂ Ω₂)) := by
  refine eq7_interchange3_generic p hp0 hp1 t
    (fun Ω₁ Ω₂ => spectralNorm (Tn3 a p Ω₁ Ω₂))
    (fun eps Ω₁ Ω₂ => spectralNorm ((8:ℝ) • Goff3 a p (swapL eps (Ω₁, Ω₂))
        (Order2.swapR eps (Ω₁, Ω₂)) (Order2.swapR eps (Ω₁, Ω₂))))
    (fun Ω₁ Ω₂ => spectralNorm ((8:ℝ) • Goff3 a p Ω₁ Ω₂ Ω₂))
    (fun Ω₁ Ω₂ => survivalM_on_swap3 a p Ω₁ Ω₂)
    ?_
    (fun Ω₁ Ω₂ eps h1 h2 => lt_of_lt_of_le h1 h2)
  intro eps
  exact Order2.pair_swap_relabel p eps
    (fun Ω₁ Ω₂ => t < spectralNorm ((8:ℝ) • Goff3 a p Ω₁ Ω₂ Ω₂))

-- ===========================================================================
-- (7) THE de la Peña ORDER-INDUCTION (eq-5 corners + eq-7 corner → 3-copy target).
-- FREEZE slot 1 (= the singleton copy): Goff3(Ω_fr, Ω₂, Ω₃) = Order2.Goff (afreeze1) Ω₂ Ω₃,
-- where afreeze1(w2,w3) = Σ_{w1 ∉ {w2,w3}} cI(Ω_fr,w1) • a w1 w2 w3.  Then the corner with
-- slots 2,3 sharing a copy is an order-2 DIAGONAL Goff, decoupled by Order2.dlp_forward_tail
-- FIBERWISE under the outer Ω_fr-integration (Fubini).
-- ===========================================================================

-- the frozen-slot-1 coefficient family.
noncomputable def afreeze1 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω_fr : Pt n1 n2) (w2 w3 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2,
    (if w1 = w2 ∨ w1 = w3 then (0 : RealMatrix n1 n2)
     else centeredIndicator Ω_fr p w1.1 w1.2 • a w1 w2 w3)

-- FREEZE IDENTITY: Goff3 a p Ω_fr Ω₂ Ω₃ = Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃.
theorem goff3_freeze1 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω_fr Ω₂ Ω₃ : Pt n1 n2) :
    Goff3 a p Ω_fr Ω₂ Ω₃ = Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃ := by
  -- RHS, unfolded.
  show (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
       else (centeredIndicator Ω_fr p w1.1 w1.2 * centeredIndicator Ω₂ p w2.1 w2.2
              * centeredIndicator Ω₃ p w3.1 w3.2) • a w1 w2 w3))
    = ∑ x : Fin n1 × Fin n2, ∑ y : Fin n1 × Fin n2,
        (if x = y then (0 : RealMatrix n1 n2)
         else (centeredIndicator Ω₂ p x.1 x.2 * centeredIndicator Ω₃ p y.1 y.2) •
           (∑ z : Fin n1 × Fin n2,
             (if z = x ∨ z = y then (0 : RealMatrix n1 n2)
              else centeredIndicator Ω_fr p z.1 z.2 • a z x y)))
  -- reorder LHS: Σ_w1 Σ_w2 Σ_w3 → Σ_w2 Σ_w3 Σ_w1.  (Finset.sum_comm twice.)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy : x = y
  · simp only [hxy, if_true]
    apply Finset.sum_eq_zero; intro z _
    rw [if_pos (by tauto)]
  · rw [if_neg hxy, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro z _
    by_cases hg : z = x ∨ z = y
    · rw [if_pos (by tauto), if_pos hg, smul_zero]
    · rw [if_neg (by tauto), if_neg hg, smul_smul]
      congr 1
      ring

-- THE INDUCTION STEP (slot-1 frozen): the pair tail of the corner Goff3(Ω_fr,Ω,Ω)
-- (singleton Ω_fr in slot 1, slots 2,3 sharing) ≤ 978·triple tail of Goff3(Ω_fr,Ω₂,Ω₃).
-- Freeze slot 1, apply Order2.dlp_forward_tail FIBERWISE under the outer Ω_fr-integration.
theorem induction_freeze1 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω_fr Ω Ω))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω_fr Ω₂ Ω₃)) := by
  -- LHS = Σ_{Ω_fr} w(Ω_fr) · bernoulliEventProb p (fun Ω => s < ‖Goff (afreeze1 Ω_fr) Ω Ω‖)
  have hLHS : bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω_fr Ω Ω))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliEventProb p (fun Ω => s < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω Ω)) := by
    unfold bernoulliPairEventProb bernoulliEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω _
    simp only [goff3_freeze1]
    by_cases h : s < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω Ω) <;>
      simp only [h, if_true, if_false] <;> ring
  -- RHS triple = Σ_{Ω_fr} w(Ω_fr) · bernoulliPairEventProb p (fun Ω₂ Ω₃ => s/12 < ‖Goff (afreeze1 Ω_fr) Ω₂ Ω₃‖)
  have hRHS : bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω_fr Ω₂ Ω₃))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃)) := by
    unfold bernoulliTripleEventProb bernoulliPairEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₂ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₃ _
    simp only [goff3_freeze1]
    by_cases h : (s/12) < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃) <;>
      simp only [h, if_true, if_false] <;> ring
  rw [hLHS, hRHS]
  have hdist : (978 : ℝ) * ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
        bernoulliPairEventProb p
          (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          (978 * bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze1 a p Ω_fr) p Ω₂ Ω₃))) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω_fr _; ring
  rw [hdist]
  apply Finset.sum_le_sum; intro Ω_fr _
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg hp0 hp1 Ω_fr)
  exact Order2.dlp_forward_tail (afreeze1 a p Ω_fr) p hp0 hp1 s

-- FREEZE slot 3.
noncomputable def afreeze3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω_fr : Pt n1 n2) (w1 w2 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  ∑ w3 : Fin n1 × Fin n2,
    (if w3 = w1 ∨ w3 = w2 then (0 : RealMatrix n1 n2)
     else centeredIndicator Ω_fr p w3.1 w3.2 • a w1 w2 w3)

theorem goff3_freeze3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ Ω_fr : Pt n1 n2) :
    Goff3 a p Ω₁ Ω₂ Ω_fr = Order2.Goff (afreeze3 a p Ω_fr) p Ω₁ Ω₂ := by
  show (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
       else (centeredIndicator Ω₁ p w1.1 w1.2 * centeredIndicator Ω₂ p w2.1 w2.2
              * centeredIndicator Ω_fr p w3.1 w3.2) • a w1 w2 w3))
    = ∑ x : Fin n1 × Fin n2, ∑ y : Fin n1 × Fin n2,
        (if x = y then (0 : RealMatrix n1 n2)
         else (centeredIndicator Ω₁ p x.1 x.2 * centeredIndicator Ω₂ p y.1 y.2) •
           (∑ z : Fin n1 × Fin n2,
             (if z = x ∨ z = y then (0 : RealMatrix n1 n2)
              else centeredIndicator Ω_fr p z.1 z.2 • a x y z)))
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy : x = y
  · simp only [hxy, if_true]
    apply Finset.sum_eq_zero; intro z _
    rw [if_pos (by tauto)]
  · rw [if_neg hxy, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro z _
    by_cases hg : z = x ∨ z = y
    · rw [if_pos (by tauto), if_pos hg, smul_zero]
    · rw [if_neg (by tauto), if_neg hg, smul_smul]

theorem induction_freeze3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω Ω Ω_fr))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₃ Ω_fr)) := by
  have hLHS : bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω Ω Ω_fr))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliEventProb p (fun Ω => s < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω Ω)) := by
    unfold bernoulliPairEventProb bernoulliEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω _
    simp only [goff3_freeze3]
    by_cases h : s < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω Ω) <;>
      simp only [h, if_true, if_false] <;> ring
  have hRHS : bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₃ Ω_fr))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω₂ Ω₃)) := by
    unfold bernoulliTripleEventProb bernoulliPairEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₂ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₃ _
    simp only [goff3_freeze3]
    by_cases h : (s/12) < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω₂ Ω₃) <;>
      simp only [h, if_true, if_false] <;> ring
  rw [hLHS, hRHS]
  have hdist : (978 : ℝ) * ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
        bernoulliPairEventProb p
          (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω₂ Ω₃))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          (978 * bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze3 a p Ω_fr) p Ω₂ Ω₃))) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω_fr _; ring
  rw [hdist]
  apply Finset.sum_le_sum; intro Ω_fr _
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg hp0 hp1 Ω_fr)
  exact Order2.dlp_forward_tail (afreeze3 a p Ω_fr) p hp0 hp1 s

-- FREEZE slot 2 (singleton in the middle): Goff3(Ω, Ω_fr, Ω), slots 1,3 share Ω.
noncomputable def afreeze2 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω_fr : Pt n1 n2) (w1 w3 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  ∑ w2 : Fin n1 × Fin n2,
    (if w2 = w1 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
     else centeredIndicator Ω_fr p w2.1 w2.2 • a w1 w2 w3)

theorem goff3_freeze2 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω_fr Ω₃ : Pt n1 n2) :
    Goff3 a p Ω₁ Ω_fr Ω₃ = Order2.Goff (afreeze2 a p Ω_fr) p Ω₁ Ω₃ := by
  show (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
       else (centeredIndicator Ω₁ p w1.1 w1.2 * centeredIndicator Ω_fr p w2.1 w2.2
              * centeredIndicator Ω₃ p w3.1 w3.2) • a w1 w2 w3))
    = ∑ x : Fin n1 × Fin n2, ∑ y : Fin n1 × Fin n2,
        (if x = y then (0 : RealMatrix n1 n2)
         else (centeredIndicator Ω₁ p x.1 x.2 * centeredIndicator Ω₃ p y.1 y.2) •
           (∑ z : Fin n1 × Fin n2,
             (if z = x ∨ z = y then (0 : RealMatrix n1 n2)
              else centeredIndicator Ω_fr p z.1 z.2 • a x z y)))
  -- reorder LHS Σ_w1 Σ_w2 Σ_w3 → Σ_w1 Σ_w3 Σ_w2 (sum_comm on the inner two).
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy : x = y
  · simp only [hxy, if_true]
    apply Finset.sum_eq_zero; intro z _
    rw [if_pos (by tauto)]
  · rw [if_neg hxy, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro z _
    by_cases hg : z = x ∨ z = y
    · rw [if_pos (by tauto), if_pos hg, smul_zero]
    · rw [if_neg (by tauto), if_neg hg, smul_smul]
      congr 1
      ring

theorem induction_freeze2 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω Ω_fr Ω))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω_fr Ω₃)) := by
  have hLHS : bernoulliPairEventProb p (fun Ω_fr Ω => s < spectralNorm (Goff3 a p Ω Ω_fr Ω))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliEventProb p (fun Ω => s < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω Ω)) := by
    unfold bernoulliPairEventProb bernoulliEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω _
    simp only [goff3_freeze2]
    by_cases h : s < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω Ω) <;>
      simp only [h, if_true, if_false] <;> ring
  have hRHS : bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω_fr Ω₃))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω₂ Ω₃)) := by
    unfold bernoulliTripleEventProb bernoulliPairEventProb
    apply Finset.sum_congr rfl; intro Ω_fr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₂ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro Ω₃ _
    simp only [goff3_freeze2]
    by_cases h : (s/12) < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω₂ Ω₃) <;>
      simp only [h, if_true, if_false] <;> ring
  rw [hLHS, hRHS]
  have hdist : (978 : ℝ) * ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
        bernoulliPairEventProb p
          (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω₂ Ω₃))
      = ∑ Ω_fr : Pt n1 n2, bernoulliObservationWeight p Ω_fr *
          (978 * bernoulliPairEventProb p
            (fun Ω₂ Ω₃ => (s/12) < spectralNorm (Order2.Goff (afreeze2 a p Ω_fr) p Ω₂ Ω₃))) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω_fr _; ring
  rw [hdist]
  apply Finset.sum_le_sum; intro Ω_fr _
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg hp0 hp1 Ω_fr)
  exact Order2.dlp_forward_tail (afreeze2 a p Ω_fr) p hp0 hp1 s

-- ===========================================================================
-- (8) FINAL ASSEMBLY.  Helpers: triple permutation relabel, triple monotonicity,
-- two-corner = Tn3 − (6 mixed corners) identity, then the 7-way union + collect.
-- ===========================================================================

-- triple-measure spectralNorm tail prob (the common target).
-- All paths reduce to `tripleTarget a p t = P_triple(t < ‖Goff3(Ω₁,Ω₂,Ω₃)‖)`.

-- threshold monotonicity for the triple tail.
theorem triple_event_prob_mono {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop)
    (hEF : ∀ Ω₁ Ω₂ Ω₃, E Ω₁ Ω₂ Ω₃ → F Ω₁ Ω₂ Ω₃) :
    bernoulliTripleEventProb p E ≤ bernoulliTripleEventProb p F := by
  unfold bernoulliTripleEventProb
  apply Finset.sum_le_sum; intro Ω₁ _
  apply Finset.sum_le_sum; intro Ω₂ _
  apply Finset.sum_le_sum; intro Ω₃ _
  have hw : 0 ≤ bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
      bernoulliObservationWeight p Ω₃ := by
    have h1 := weight_nonneg hp0 hp1 Ω₁
    have h2 := weight_nonneg hp0 hp1 Ω₂
    have h3 := weight_nonneg hp0 hp1 Ω₃
    positivity
  by_cases hE : E Ω₁ Ω₂ Ω₃
  · rw [if_pos hE, if_pos (hEF Ω₁ Ω₂ Ω₃ hE)]
  · rw [if_neg hE]
    have : (0:ℝ) ≤ (if F Ω₁ Ω₂ Ω₃ then (1:ℝ) else 0) := by split <;> norm_num
    nlinarith [hw]

-- triple permutation relabels (all preserve the prob by symmetry of the product measure).
theorem triple_perm_213 {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => E Ω₂ Ω₁ Ω₃)
      = bernoulliTripleEventProb p E := by
  unfold bernoulliTripleEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω₁ _
  apply Finset.sum_congr rfl; intro Ω₂ _
  apply Finset.sum_congr rfl; intro Ω₃ _
  ring_nf

theorem triple_perm_132 {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => E Ω₁ Ω₃ Ω₂)
      = bernoulliTripleEventProb p E := by
  unfold bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω₂ _
  apply Finset.sum_congr rfl; intro Ω₃ _
  ring_nf

theorem triple_perm_231 {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => E Ω₂ Ω₃ Ω₁)
      = bernoulliTripleEventProb p E := by
  -- E' := fun a b c => E a c b.  (perm_213 E') : P(fun a b c => E' b a c) = P E'; E' b a c = E b c a.
  -- (perm_132 E) : P E' = P E.
  have h1 := triple_perm_213 p (fun a b c => E a c b)
  have h2 := triple_perm_132 p E
  rw [h1, h2]

theorem triple_perm_321 {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => E Ω₃ Ω₂ Ω₁)
      = bernoulliTripleEventProb p E := by
  -- G := fun a b c => E b c a.  (perm_132 G) : P(fun a b c => G a c b) = P G; G a c b = E c b a.
  have h1 := triple_perm_132 p (fun a b c => E b c a)
  have h2 := triple_perm_231 p E
  rw [h1, h2]

theorem triple_perm_312 {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliTripleEventProb p (fun Ω₁ Ω₂ Ω₃ => E Ω₃ Ω₁ Ω₂)
      = bernoulliTripleEventProb p E := by
  -- (312) = (231)∘(231).  G := fun a b c => E b c a; (perm_231 G) b c a = E c a b.
  have h1 := triple_perm_231 p (fun a b c => E b c a)
  have h2 := triple_perm_231 p E
  rw [h1, h2]

-- ===========================================================================
-- (8a) Tn3 = the eight-corner sum (expand (A+B)(A+B)(A+B) per index).
-- ===========================================================================
theorem Tn3_eq_eight_corners {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    Tn3 a p Ω₁ Ω₂
      = Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁
        + Goff3 a p Ω₁ Ω₂ Ω₂ + Goff3 a p Ω₂ Ω₁ Ω₂ + Goff3 a p Ω₂ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂ := by
  unfold Tn3 Goff3
  -- distribute the 8 corner-sums into one, termwise.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w3 _
  by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
  · simp [h]
  · simp only [h, if_false]
    rw [← add_smul, ← add_smul, ← add_smul, ← add_smul, ← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- the two diagonal corners = Tn3 − (the 6 mixed corners).
theorem two_corner3_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂
      = Tn3 a p Ω₁ Ω₂
        - (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁
           + Goff3 a p Ω₁ Ω₂ Ω₂ + Goff3 a p Ω₂ Ω₁ Ω₂ + Goff3 a p Ω₂ Ω₂ Ω₁) := by
  rw [Tn3_eq_eight_corners]; abel

-- ===========================================================================
-- (8b) ROUTING: each corner (+ the Tn3 term) → the common triple target
--      Tgt(τ) = P_triple(τ < ‖Goff3(Ω₁,Ω₂,Ω₃)‖), at threshold s/1152.
-- ===========================================================================

-- pair-event: rescale ‖8•X‖ threshold to ‖X‖.
theorem pair_eightsmul_eq {n1 n2 : ℕ} (p : ℝ) (t : ℝ)
    (X : Pt n1 n2 → Pt n1 n2 → RealMatrix n1 n2) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm ((8:ℝ) • X Ω₁ Ω₂))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => t/8 < spectralNorm (X Ω₁ Ω₂)) := by
  unfold bernoulliPairEventProb
  apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
  have hiff : (t < spectralNorm ((8:ℝ) • X Ω₁ Ω₂)) ↔ (t/8 < spectralNorm (X Ω₁ Ω₂)) := by
    rw [Order2.spectralNorm_smul]
    have h8 : |(8:ℝ)| = 8 := by norm_num
    rw [h8]; constructor <;> intro h <;> linarith
  rw [show (if t < spectralNorm ((8:ℝ) • X Ω₁ Ω₂) then (1:ℝ) else 0)
        = (if t/8 < spectralNorm (X Ω₁ Ω₂) then (1:ℝ) else 0) from by
    by_cases h : t/8 < spectralNorm (X Ω₁ Ω₂)
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]]

-- THE Tn3 PATH: P_pair(t<‖Tn3‖) ≤ 2916·978·P_triple(t/96 < ‖Goff3(Ω₁,Ω₂,Ω₃)‖).
theorem tn3_path {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn3 a p Ω₁ Ω₂))
      ≤ (2916 * 978) * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/8/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  -- eq7: (1/2916)·P(t<‖Tn3‖) ≤ P(t<‖8•Goff3(Ω₁,Ω₂,Ω₂)‖)
  have hE7 := eq7_interchange3 a p hp0 hp1 t
  rw [pair_eightsmul_eq] at hE7
  -- so P(t<‖Tn3‖) ≤ 2916·P(t/8<‖Goff3(Ω₁,Ω₂,Ω₂)‖)
  have hTn3 : bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn3 a p Ω₁ Ω₂))
      ≤ 2916 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => t/8 < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)) := by
    nlinarith [hE7]
  -- induction_freeze1 on Goff3(Ω_fr,Ω,Ω): P(Ω_fr Ω => u<‖Goff3(Ω_fr,Ω,Ω)‖) ≤ 978·P_triple(u/12<‖Goff3‖)
  have hind := induction_freeze1 a p hp0 hp1 (t/8)
  -- chain.
  calc bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn3 a p Ω₁ Ω₂))
      ≤ 2916 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => t/8 < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)) := hTn3
    _ ≤ 2916 * (978 * bernoulliTripleEventProb p
          (fun Ω_fr Ω₂ Ω₃ => (t/8/12) < spectralNorm (Goff3 a p Ω_fr Ω₂ Ω₃))) := by
        apply mul_le_mul_of_nonneg_left hind (by norm_num)
    _ = (2916 * 978) * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/8/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by ring

-- ===========================================================================
-- (8c) The 6 mixed-corner routings.  Each: (optional pair swap) + induction_freezeK
--      + triple perm relabel → ≤ 978 · P_triple(t/12 < ‖Goff3(Ω₁,Ω₂,Ω₃)‖).
-- ===========================================================================

-- corner (1,1,2): singleton Ω₂ in slot 3 → freeze3, swap.  triple target Goff3(b,c,a)=perm_231.
theorem corner_112 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  have hsw : bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂))
      = bernoulliPairEventProb p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω Ω Ω_fr)) :=
    Order2.pair_swap_args p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω Ω Ω_fr))
  refine le_trans (le_of_eq hsw) (le_trans (induction_freeze3 a p hp0 hp1 t) (le_of_eq ?_))
  rw [triple_perm_231 p (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃))]

-- corner (1,2,1): singleton Ω₂ in slot 2 → freeze2, swap.  triple target Goff3(b,a,c)=perm_213.
theorem corner_121 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  have hsw : bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁))
      = bernoulliPairEventProb p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω Ω_fr Ω)) :=
    Order2.pair_swap_args p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω Ω_fr Ω))
  refine le_trans (le_of_eq hsw) (le_trans (induction_freeze2 a p hp0 hp1 t) (le_of_eq ?_))
  rw [triple_perm_213 p (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃))]

-- corner (2,1,1): singleton Ω₂ in slot 1 → freeze1, swap.  triple target Goff3(a,b,c)=canonical.
theorem corner_211 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  have hsw : bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁))
      = bernoulliPairEventProb p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω_fr Ω Ω)) :=
    Order2.pair_swap_args p (fun Ω_fr Ω => t < spectralNorm (Goff3 a p Ω_fr Ω Ω))
  exact le_trans (le_of_eq hsw) (induction_freeze1 a p hp0 hp1 t)

-- corner (1,2,2): singleton Ω₁ in slot 1 → freeze1, NO swap.  canonical.
theorem corner_122 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) :=
  induction_freeze1 a p hp0 hp1 t

-- corner (2,1,2): singleton Ω₁ in slot 2 → freeze2, NO swap.  triple target Goff3(b,a,c)=perm_213.
theorem corner_212 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  refine le_trans (induction_freeze2 a p hp0 hp1 t) ?_
  rw [triple_perm_213 p (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃))]

-- corner (2,2,1): singleton Ω₁ in slot 3 → freeze3, NO swap.  triple target Goff3(b,c,a)=perm_231.
theorem corner_221 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁))
      ≤ 978 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  refine le_trans (induction_freeze3 a p hp0 hp1 t) ?_
  rw [triple_perm_231 p (fun Ω₁ Ω₂ Ω₃ => (t/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃))]

-- ===========================================================================
-- (8d) 7-way pair union: the two-corner tail ⊆ (Tn3) ∪ (6 mixed corners), thr s/12.
-- ===========================================================================
theorem two_corner_union7 {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (s : ℝ) :
    bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Tn3 a p Ω₁ Ω₂))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂))
        + bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁)) := by
  unfold bernoulliPairEventProb
  -- distribute the 7-term RHS sum into one double sum.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₁ _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₂ _
  set w := bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ with hw
  have hwnn : 0 ≤ w := mul_nonneg (weight_nonneg hp0 hp1 _) (weight_nonneg hp0 hp1 _)
  -- the union cover: 2s/3 < ‖two-corner‖ ⇒ one of the 7 pieces exceeds s/12.
  have hcover : (2*s/3) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂)
      → (s/12) < spectralNorm (Tn3 a p Ω₁ Ω₂)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂)
        ∨ (s/12) < spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁) := by
    intro htc
    by_contra hcon; push_neg at hcon
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hcon
    -- two-corner = Tn3 − R; ‖two-corner‖ ≤ ‖Tn3‖ + Σ6 ‖corner‖ ≤ 7·(s/12) = 7s/12 < 2s/3.
    have heq := two_corner3_eq a p Ω₁ Ω₂
    have htri1 : spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂)
        ≤ spectralNorm (Tn3 a p Ω₁ Ω₂)
          + spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁
             + Goff3 a p Ω₁ Ω₂ Ω₂ + Goff3 a p Ω₂ Ω₁ Ω₂ + Goff3 a p Ω₂ Ω₂ Ω₁) := by
      rw [heq]; exact Order2.spectralNorm_sub_tri _ _
    -- expand the 6-fold triangle on R.
    have htriR : spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁
             + Goff3 a p Ω₁ Ω₂ Ω₂ + Goff3 a p Ω₂ Ω₁ Ω₂ + Goff3 a p Ω₂ Ω₂ Ω₁)
        ≤ spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂) + spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁)
          + spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁) + spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)
          + spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂) + spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁) := by
      refine le_trans (Order2.spectralNorm_tri _ _) ?_
      have t1 := Order2.spectralNorm_tri (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁
        + Goff3 a p Ω₁ Ω₂ Ω₂) (Goff3 a p Ω₂ Ω₁ Ω₂)
      have t2 := Order2.spectralNorm_tri (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁ + Goff3 a p Ω₂ Ω₁ Ω₁)
        (Goff3 a p Ω₁ Ω₂ Ω₂)
      have t3 := Order2.spectralNorm_tri (Goff3 a p Ω₁ Ω₁ Ω₂ + Goff3 a p Ω₁ Ω₂ Ω₁) (Goff3 a p Ω₂ Ω₁ Ω₁)
      have t4 := Order2.spectralNorm_tri (Goff3 a p Ω₁ Ω₁ Ω₂) (Goff3 a p Ω₁ Ω₂ Ω₁)
      linarith
    have : spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂) ≤ 7*(s/12) := by
      linarith [htri1, htriR, h0, h1, h2, h3, h4, h5, h6]
    have hTn3nn : (0:ℝ) ≤ spectralNorm (Tn3 a p Ω₁ Ω₂) := by
      unfold spectralNorm; exact norm_nonneg _
    linarith
  by_cases hE : (2*s/3) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂)
  · have hor := hcover hE
    rw [if_pos hE]
    -- RHS ≥ w·1 (at least one indicator is 1).
    have hnn : ∀ (P : Prop) [Decidable P], (0:ℝ) ≤ w * (if P then (1:ℝ) else 0) := by
      intro P _; apply mul_nonneg hwnn; split <;> norm_num
    rcases hor with h | h | h | h | h | h | h <;>
      simp only [if_pos h] <;>
      nlinarith [hnn ((s/12) < spectralNorm (Tn3 a p Ω₁ Ω₂)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂)),
        hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁)), hwnn]
  · rw [if_neg hE]
    have hnn : ∀ (P : Prop) [Decidable P], (0:ℝ) ≤ w * (if P then (1:ℝ) else 0) := by
      intro P _; apply mul_nonneg hwnn; split <;> norm_num
    nlinarith [hnn ((s/12) < spectralNorm (Tn3 a p Ω₁ Ω₂)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₂)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₁)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₁)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₂)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₁ Ω₂)),
      hnn ((s/12) < spectralNorm (Goff3 a p Ω₂ Ω₂ Ω₁))]

-- ===========================================================================
-- (8e) THE ORDER-3 FORWARD TAIL: diagonal ≤ L·P_triple(decoupled), threshold /1152.
--   L = 3·(2916·978 + 6·978) = 3·978·2922 = 8573148.   (for s ≥ 0.)
-- ===========================================================================
theorem dlp_forward_tail3 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (Goff3 a p Ω Ω Ω))
      ≤ 8573148 * bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => (s/1152) < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) := by
  -- abbreviation for the common target tail.
  set Tgt : ℝ → ℝ := fun τ => bernoulliTripleEventProb p
    (fun Ω₁ Ω₂ Ω₃ => τ < spectralNorm (Goff3 a p Ω₁ Ω₂ Ω₃)) with hTgt
  -- Step 1: Lemma 1 (3-copy).
  have hL1 : bernoulliEventProb p (fun Ω => s < spectralNorm (Goff3 a p Ω Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂)) :=
    Order2.L1Diag.lemma1_diag_3copy p hp0 hp1 (fun Ω => Goff3 a p Ω Ω Ω) s
  -- Step 2: 7-way union (threshold s/12).
  have hU := two_corner_union7 hp0 hp1 a s
  -- Step 3a: Tn3 path at t = s/12  →  2916·978·Tgt(s/12/8/12) = 2916·978·Tgt(s/1152).
  have hTn3 := tn3_path a p hp0 hp1 (s/12)
  have heqT : (s/12/8/12) = s/1152 := by ring
  rw [heqT] at hTn3
  -- Step 3b: corners at t = s/12  →  978·Tgt(s/12/12) = 978·Tgt(s/144).  Then mono to Tgt(s/1152).
  have hmono : Tgt (s/144) ≤ Tgt (s/1152) := by
    rw [hTgt]
    apply triple_event_prob_mono hp0 hp1
    intro Ω₁ Ω₂ Ω₃ h
    have : s/1152 ≤ s/144 := by linarith
    linarith
  have hc1 := corner_112 a p hp0 hp1 (s/12)
  have hc2 := corner_121 a p hp0 hp1 (s/12)
  have hc3 := corner_211 a p hp0 hp1 (s/12)
  have hc4 := corner_122 a p hp0 hp1 (s/12)
  have hc5 := corner_212 a p hp0 hp1 (s/12)
  have hc6 := corner_221 a p hp0 hp1 (s/12)
  have heqc : (s/12/12) = s/144 := by ring
  rw [heqc] at hc1 hc2 hc3 hc4 hc5 hc6
  -- nonneg of Tgt.
  have hTgtnn : ∀ τ, 0 ≤ Tgt τ := by
    intro τ; rw [hTgt]; unfold bernoulliTripleEventProb
    apply Finset.sum_nonneg; intro Ω₁ _; apply Finset.sum_nonneg; intro Ω₂ _
    apply Finset.sum_nonneg; intro Ω₃ _
    have hw : 0 ≤ bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
        bernoulliObservationWeight p Ω₃ := by
      have h1 := weight_nonneg hp0 hp1 Ω₁; have h2 := weight_nonneg hp0 hp1 Ω₂
      have h3 := weight_nonneg hp0 hp1 Ω₃; positivity
    apply mul_nonneg hw; split <;> norm_num
  -- combine.  Each corner ≤ 978·Tgt(s/144) ≤ 978·Tgt(s/1152); Tn3 ≤ 2916·978·Tgt(s/1152).
  have hbig : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm
        (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂))
      ≤ (2916*978 + 6*978) * Tgt (s/1152) := by
    have hmTn3 : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Tn3 a p Ω₁ Ω₂))
        ≤ (2916*978) * Tgt (s/1152) := hTn3
    have e1 := le_trans hc1 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    have e2 := le_trans hc2 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    have e3 := le_trans hc3 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    have e4 := le_trans hc4 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    have e5 := le_trans hc5 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    have e6 := le_trans hc6 (by nlinarith [hmono] : (978:ℝ) * Tgt (s/144) ≤ 978 * Tgt (s/1152))
    nlinarith [hU, hmTn3, e1, e2, e3, e4, e5, e6]
  calc bernoulliEventProb p (fun Ω => s < spectralNorm (Goff3 a p Ω Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff3 a p Ω₁ Ω₁ Ω₁ + Goff3 a p Ω₂ Ω₂ Ω₂)) := hL1
    _ ≤ 3 * ((2916*978 + 6*978) * Tgt (s/1152)) := by
        apply mul_le_mul_of_nonneg_left hbig (by norm_num)
    _ = 8573148 * Tgt (s/1152) := by ring

end Prove55

open Prove55

-- ===========================================================================
-- (9) FINAL THEOREM — 55f0c9c3's survival form (K = 1152, L = 8573148), via the
-- complement of dlp_forward_tail3.  Order-3 de la Peña–Montgomery-Smith forward
-- decoupling (arXiv:math/9309211, §4, k=3), all bricks Proved.
-- ===========================================================================
theorem solution :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ : ℕ}
        (G : Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        (∃ a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
               (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂,
            ∀ Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
              G Omega1 Omega2 Omega3 =
                ∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  ∑ w3 : Fin n₁ × Fin n₂,
                  (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then
                      (0 : RealMatrix n₁ n₂)
                   else
                     (centeredIndicator Omega1 p w1.1 w1.2 *
                       centeredIndicator Omega2 p w2.1 w2.2 *
                       centeredIndicator Omega3 p w3.1 w3.2) • a w1 w2 w3)) →
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm (G Omega1 Omega2 Omega3) ≤ Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (G Omega Omega Omega) ≤ (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  refine ⟨1152, 8573148, by norm_num, by norm_num, ?_⟩
  intro n₁ n₂ G p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec hrep htriple
  obtain ⟨a, ha⟩ := hrep
  -- G = Goff3 a p (off-diagonal trilinear representation).
  have hG : ∀ Ω₁ Ω₂ Ω₃, G Ω₁ Ω₂ Ω₃ = Goff3 a p Ω₁ Ω₂ Ω₃ := by
    intro Ω₁ Ω₂ Ω₃; rw [ha]; rfl
  -- triple tail (strict complement of the hyp): P_triple(Cdec·thr < ‖G‖) ≤ cdec·fail.
  have htriple_tail : bernoulliTripleEventProb p
      (fun Ω₁ Ω₂ Ω₃ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂ Ω₃))
        ≤ cdec * failureScale := by
    have hc := triple_event_prob_add_compl p
      (fun Ω₁ Ω₂ Ω₃ => spectralNorm (G Ω₁ Ω₂ Ω₃) ≤ Cdec * thresholdScale)
    have heq : bernoulliTripleEventProb p
        (fun Ω₁ Ω₂ Ω₃ => ¬ (spectralNorm (G Ω₁ Ω₂ Ω₃) ≤ Cdec * thresholdScale))
      = bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂ Ω₃)) := by
      unfold bernoulliTripleEventProb
      apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
      apply Finset.sum_congr rfl; intro Ω₃ _
      congr 1; simp only [not_le]
    rw [heq] at hc
    have : (1:ℝ) - cdec * failureScale ≤
        bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => spectralNorm (G Ω₁ Ω₂ Ω₃) ≤ Cdec * thresholdScale) := htriple
    linarith [hc]
  -- The diagonal strict tail ≤ (8573148·cdec)·fail.  Two cases on the sign of the threshold.
  have hdiag_tail : bernoulliEventProb p
      (fun Ω => (1152 * Cdec * thresholdScale) < spectralNorm (G Ω Ω Ω))
        ≤ (8573148 * cdec) * failureScale := by
    rcases le_or_gt 0 (1152 * Cdec * thresholdScale) with hs | hs
    · -- s ≥ 0: use the forward tail.
      have hfwd := dlp_forward_tail3 a p hp0 hp1 (1152 * Cdec * thresholdScale) hs
      have hs1152 : (1152 * Cdec * thresholdScale) / 1152 = Cdec * thresholdScale := by ring
      rw [hs1152] at hfwd
      have hGdiag : ∀ Ω : Prove55.Pt n₁ n₂, Goff3 a p Ω Ω Ω = G Ω Ω Ω :=
        fun Ω => (hG Ω Ω Ω).symm
      have hGtrip : ∀ Ω₁ Ω₂ Ω₃ : Prove55.Pt n₁ n₂, Goff3 a p Ω₁ Ω₂ Ω₃ = G Ω₁ Ω₂ Ω₃ :=
        fun Ω₁ Ω₂ Ω₃ => (hG Ω₁ Ω₂ Ω₃).symm
      simp only [hGdiag, hGtrip] at hfwd
      calc bernoulliEventProb p (fun Ω => (1152 * Cdec * thresholdScale) < spectralNorm (G Ω Ω Ω))
          ≤ 8573148 * bernoulliTripleEventProb p
              (fun Ω₁ Ω₂ Ω₃ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂ Ω₃)) := hfwd
        _ ≤ 8573148 * (cdec * failureScale) := by
            apply mul_le_mul_of_nonneg_left htriple_tail (by norm_num)
        _ = (8573148 * cdec) * failureScale := by ring
    · -- s < 0: BOTH the diagonal strict tail AND the triple strict tail are always-true
      -- (‖·‖ ≥ 0 > s), so the diagonal prob = 1 and the hyp forces cdec·fail ≥ 1.
      have hdone : bernoulliEventProb p
          (fun Ω => (1152 * Cdec * thresholdScale) < spectralNorm (G Ω Ω Ω)) = 1 := by
        rw [← weights_sum_one (n1 := n₁) (n2 := n₂) p]
        unfold bernoulliEventProb
        apply Finset.sum_congr rfl; intro Ω _
        have hnn : (0:ℝ) ≤ spectralNorm (G Ω Ω Ω) := by unfold spectralNorm; exact norm_nonneg _
        simp only [if_pos (show (1152 * Cdec * thresholdScale) < spectralNorm (G Ω Ω Ω) by linarith),
          mul_one]
      rw [hdone]
      -- the triple strict tail is also always-true ⇒ P_triple = 1 ⇒ htriple_tail : 1 ≤ cdec·fail.
      have hone : bernoulliTripleEventProb p
          (fun Ω₁ Ω₂ Ω₃ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂ Ω₃)) = 1 := by
        rw [← Prove55.triple_weights_sum_one (n1 := n₁) (n2 := n₂) p]
        unfold bernoulliTripleEventProb
        apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
        apply Finset.sum_congr rfl; intro Ω₃ _
        have hnn : (0:ℝ) ≤ spectralNorm (G Ω₁ Ω₂ Ω₃) := by
          unfold spectralNorm; exact norm_nonneg _
        -- Cdec·thr < 0 since Cdec > 0 and thr < 0 (from s = 1152·Cdec·thr < 0).
        have hthr : thresholdScale < 0 := by nlinarith [hs, hCdec]
        rw [if_pos (by nlinarith [hnn, hCdec, hthr]), mul_one]
      rw [hone] at htriple_tail
      -- htriple_tail : 1 ≤ cdec·fail.  So (8573148·cdec)·fail = 8573148·(cdec·fail) ≥ 8573148 ≥ 1.
      nlinarith [htriple_tail]
  -- complement back to the survival-form goal.
  rw [ge_iff_le]
  have hcompl := event_prob_add_compl p
    (fun Ω => spectralNorm (G Ω Ω Ω) ≤ (1152 * Cdec) * thresholdScale)
  have hcompl_eq : bernoulliEventProb p
      (fun Ω => ¬ (spectralNorm (G Ω Ω Ω) ≤ (1152 * Cdec) * thresholdScale))
    = bernoulliEventProb p
        (fun Ω => (1152 * Cdec * thresholdScale) < spectralNorm (G Ω Ω Ω)) := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl; intro Ω _
    have hassoc : (1152 * Cdec) * thresholdScale = 1152 * Cdec * thresholdScale := by ring
    simp only [not_le, hassoc]
  rw [hcompl_eq] at hcompl
  linarith [hcompl, hdiag_tail]
