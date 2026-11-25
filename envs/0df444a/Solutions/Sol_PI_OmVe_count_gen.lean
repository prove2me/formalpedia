-- Prove2me | solution 1 for PI.OmVe.count_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:33.766335+00:00
-- url     : https://prove2.me/submissions/3e49be22-089c-470e-98c7-a485f15b3faa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CardAndAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Theorems.Thm_PI_OmVe_card_and_add
import Theorems.Thm_PI_OmVe_card_perp
import Theorems.Thm_PI_OmVe_card_split
import Theorems.Thm_PI_OmVe_det_corOne
import Theorems.Thm_PI_OmVe_indep_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (haM : a' ≤ M)
    {k : Type} [Finite k] [Zero k] (ι : k → K) (hι : Function.Injective ι) (hι0 : ι 0 = 0)
    (hrange : ∀ x : Fin M → K, ∃ c, ffH σ J x x = ι c) (N D : ℕ)
    (hN : ∀ c, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram σ J X = T + Matrix.single i₀ i₀ (ι c)} = N)
    (hD : ∀ Y : Fin a' → Fin M → K, ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y j) x = 0) ∧ ffH σ J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = D) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} * D +
      (Nat.card k - 1) * N =
    Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} *
      Nat.card K ^ (M - a') := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype k := Fintype.ofFinite k
  set T0 := T.submatrix i₀.succAbove i₀.succAbove with hT0
  have hu0 : IsUnit T0.det := by
    have h1 := det_corOne T i₀ hr (1 : K)
    rw [one_mul] at h1
    rw [← h1]
    exact hu
  let A : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} → k → ℕ := fun Y c =>
    Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = ι c}
  have hperp : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = Nat.card K ^ (M - a') := by
    intro Y
    have h1 := card_perp σ J T0 hu0 Y.1 Y.2
    have hK : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card K ^ M = Nat.card K ^ (M - a') * Nat.card K ^ a' := by
      rw [← pow_add, Nat.sub_add_cancel haM]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hK _) h1
  have hfib : ∀ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
      Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y.1 j) x = 0} = ∑ c, A Y c := by
    intro Y
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ffH σ J x x) (t := Finset.univ.image ι)
      (fun x _ => by
        obtain ⟨c, hc'⟩ := hrange x
        exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc'.symm⟩)]
    rw [Finset.sum_image (fun a _ b _ h => hι h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.filter_filter]
  have htot : Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * Nat.card K ^ (M - a') =
      ∑ c, ∑ Y, A Y c := by
    rw [Finset.sum_comm, Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [← hperp Y, hfib Y]
  have hcN : ∀ c, c ≠ 0 → ∑ Y, A Y c = N := by
    intro c hc0
    rw [← hN c hc0]
    have h1 := card_split σ J hσ hJ T i₀ hr hc (ι c) (fun _ => True)
    simp only [and_true] at h1
    rw [h1, Nat.card_sigma]
  have h0 : ∑ Y, A Y 0 = Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
    have hR := card_split σ J hσ hJ T i₀ hr hc 0 (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [Matrix.single_zero, add_zero] at hR
    have hLI : Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} =
        Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ ∀ c : K, c • X i₀ = 0 → c = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).1 h.2⟩,
          fun h => ⟨h.1, (indep_iff σ J i₀ hc hu X h.1).2 h.2⟩⟩)
    have hD' : ∑ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T0},
        Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0 ∧
          ¬ ∀ c : K, c • x = 0 → c = 0} =
        Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T0} * D := by
      rw [Finset.sum_congr rfl (fun Y _ => hD Y.1 Y.2), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, Nat.card_eq_fintype_card]
    rw [hLI, hR, Nat.card_sigma, ← hD', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [A, hι0]
    have h2 := card_and_add (fun x : Fin M → K => (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = 0)
      (fun x => ∀ c : K, c • x = 0 → c = 0)
    simp only [and_assoc] at h2
    exact h2.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)),
    Finset.sum_congr rfl (fun c hc0 => hcN c (Finset.ne_of_mem_erase hc0)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, h0] at htot
  rw [htot, Nat.card_eq_fintype_card (α := k)]
end PI.OmVe
