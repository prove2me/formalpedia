-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P06.fidelityContinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:36:08.693807+00:00
-- url     : https://prove2.me/submissions/f715c3fb-6bdf-4d8e-bd4d-b48e4e1894e9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

noncomputable section

open MeasureTheory

namespace X7P06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open QAlgorithms.Papers.Independent.Claimed50.P06

abbrev S (A : StarSubalgebra ℂ (H →L[ℂ] H)) :=
  {x : (H →L[ℂ] H) // (x ∈ Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1}

theorem ne (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Nonempty (S A) :=
  ⟨⟨0, fun a _ => by simp, by simp⟩⟩

theorem term_le (x : H →L[ℂ] H) (hx : ‖x‖ ≤ 1) (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖inner ℂ v (x w)‖ ≤ 1 := by
  calc ‖inner ℂ v (x w)‖ ≤ ‖v‖ * ‖x w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖x‖ * ‖w‖) := by gcongr; exact x.le_opNorm w
    _ ≤ 1 := by rw [hv, hw]; nlinarith [norm_nonneg x]

theorem term_diff (x : H →L[ℂ] H) (hx : ‖x‖ ≤ 1) (p1 p2 q1 q2 : H)
    (hp2 : ‖p2‖ = 1) (hq1 : ‖q1‖ = 1) :
    ‖inner ℂ p1 (x q1)‖ ≤ ‖inner ℂ p2 (x q2)‖ + (‖q1 - q2‖ + ‖p1 - p2‖) := by
  have h1 : inner ℂ p1 (x q1) = inner ℂ (p1 - p2) (x q1) + inner ℂ p2 (x (q1 - q2))
      + inner ℂ p2 (x q2) := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  have a1 : ‖inner ℂ (p1 - p2) (x q1)‖ ≤ ‖p1 - p2‖ := by
    calc _ ≤ ‖p1 - p2‖ * ‖x q1‖ := norm_inner_le_norm _ _
      _ ≤ ‖p1 - p2‖ * (‖x‖ * ‖q1‖) := by gcongr; exact x.le_opNorm _
      _ ≤ ‖p1 - p2‖ := by
        rw [hq1, mul_one]; nlinarith [norm_nonneg (p1 - p2)]
  have a2 : ‖inner ℂ p2 (x (q1 - q2))‖ ≤ ‖q1 - q2‖ := by
    calc _ ≤ ‖p2‖ * ‖x (q1 - q2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖p2‖ * (‖x‖ * ‖q1 - q2‖) := by gcongr; exact x.le_opNorm _
      _ ≤ ‖q1 - q2‖ := by
        rw [hp2, one_mul]; nlinarith [norm_nonneg (q1 - q2)]
  rw [h1]
  calc _ ≤ ‖inner ℂ (p1 - p2) (x q1) + inner ℂ p2 (x (q1 - q2))‖ + ‖inner ℂ p2 (x q2)‖ :=
        norm_add_le _ _
    _ ≤ ‖inner ℂ (p1 - p2) (x q1)‖ + ‖inner ℂ p2 (x (q1 - q2))‖ + ‖inner ℂ p2 (x q2)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

theorem bdd (A : StarSubalgebra ℂ (H →L[ℂ] H)) (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    BddAbove (Set.range fun x : S A => ‖inner ℂ v (x.val w)‖) :=
  ⟨1, by rintro _ ⟨x, rfl⟩; exact term_le x.val x.2.2 v w hv hw⟩

theorem one_side (A : StarSubalgebra ℂ (H →L[ℂ] H)) (p1 p2 q1 q2 : H)
    (hp1 : ‖p1‖ = 1) (hp2 : ‖p2‖ = 1) (hq1 : ‖q1‖ = 1) (hq2 : ‖q2‖ = 1) :
    vectorFidelity A p1 q1 ≤ vectorFidelity A p2 q2 + (‖q1 - q2‖ + ‖p1 - p2‖) := by
  haveI := ne A
  unfold vectorFidelity
  apply ciSup_le
  intro x
  have := term_diff x.val x.2.2 p1 p2 q1 q2 hp2 hq1
  have h2 : ‖inner ℂ p2 (x.val q2)‖ ≤ ⨆ y : S A, ‖inner ℂ p2 (y.val q2)‖ :=
    le_ciSup (bdd A p2 q2 hp2 hq2) x
  linarith

end X7P06

namespace QAlgorithms.Papers.Independent.Claimed50.P06
end QAlgorithms.Papers.Independent.Claimed50.P06

open QAlgorithms.Papers.Independent.Claimed50.P06 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (psi1 psi2 phi1 phi2 : H)
    (hPsi1 : ‖psi1‖ = 1) (hPsi2 : ‖psi2‖ = 1)
    (hPhi1 : ‖phi1‖ = 1) (hPhi2 : ‖phi2‖ = 1) :
    |vectorFidelity A psi1 phi1 - vectorFidelity A psi2 phi2| ≤
      ‖phi1 - phi2‖ + ‖psi1 - psi2‖ := by
  have a := X7P06.one_side A psi1 psi2 phi1 phi2 hPsi1 hPsi2 hPhi1 hPhi2
  have b := X7P06.one_side A psi2 psi1 phi2 phi1 hPsi2 hPsi1 hPhi2 hPhi1
  rw [norm_sub_rev phi2, norm_sub_rev psi2] at b
  rw [abs_le]; constructor <;> linarith

end
