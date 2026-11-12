-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P47.se_channel_preserves
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:52:04.629549+00:00
-- url     : https://prove2.me/submissions/2b008b51-469e-4e69-b7ab-5d5795121754

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}
variable [Fintype G] [Group G] [DecidableEq G]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype P] [DecidableEq P] [Nonempty P]
variable [Fintype T] [DecidableEq T] [Nonempty T]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype R2] [DecidableEq R2] [Nonempty R2]
variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

namespace Aux_SE_P47

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P47

theorem chan_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  rw [hΦE]
  unfold krausApply IsDensityMatrix
  constructor
  · apply Matrix.posSemidef_sum
    intro j _
    exact hρ.1.mul_mul_conjTranspose_same (E j)
  · have h : ∀ j, (E j * ρ * (E j)ᴴ).trace = ((E j)ᴴ * E j * ρ).trace := by
      intro j
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [Matrix.trace_sum, Finset.sum_congr rfl (fun j _ => h j), ← Matrix.trace_sum,
      ← Finset.sum_mul, hE, Matrix.one_mul]
    exact hρ.2

theorem se_preserves [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2]
    (U : G → Mat (R × S)) (V : G → Mat (R2 × S2)) (N : Superop S S2)
    (hN : SEChannel U V N) (rho : Mat S) (hrho : SE U rho) : SE V (N rho) := by
  obtain ⟨hρ, w0, ⟨hw, hwsym⟩, hwtr⟩ := hrho
  obtain ⟨hNch, M, ⟨hMch, hMtr⟩, hcov⟩ := hN
  unfold SE Extension QAlgorithms.Papers.Independent.Extend50.P47.Sym
  refine ⟨chan_density N hNch rho hρ, M w0, ⟨chan_density M hMch w0 hw, fun g => ?_⟩, ?_⟩
  · calc M w0 = M (U g * w0 * (U g)ᴴ) := by rw [← hwsym g]
      _ = V g * M w0 * (V g)ᴴ := hcov g w0
  · rw [hMtr, hwtr]

end Aux_SE_P47

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P47 in
theorem solution [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (U : G → Matrix.unitaryGroup (R × S) ℂ)
    (V : G → Matrix.unitaryGroup (R2 × S2) ℂ) (hU : IsProjectiveUnitaryLift U) (hV : IsProjectiveUnitaryLift V)
    (N : Superop S S2) (hN : SEChannel (fun g => (U g : Mat (R × S)))
      (fun g => (V g : Mat (R2 × S2))) N)
    (rho : Mat S) (hrho : SE (fun g => (U g : Mat (R × S))) rho) :
    SE (fun g => (V g : Mat (R2 × S2))) (N rho) :=
  Aux_SE_P47.se_preserves _ _ N hN rho hrho

end
