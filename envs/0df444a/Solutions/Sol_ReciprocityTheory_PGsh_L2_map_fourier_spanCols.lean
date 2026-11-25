-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.map_fourier_spanCols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:47.42072+00:00
-- url     : https://prove2.me/submissions/77cc0db6-d408-4221-b2ab-5d5a5788bfa1

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem fourier_column_eq (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) (h : H)
    (j : N) :
    fourier (R := R) (fun h a => e h a) (fun x => Dm x j) h =
      ((tableM e σ)ᵀ * Dm) (σ h) j := by
  simp only [fourier_apply', Matrix.mul_apply, Matrix.transpose_apply, tableM,
    Matrix.of_apply, Equiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) :
    (Submodule.span R (Set.range fun j x => Dm x j)).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => ((tableM e σ)ᵀ * Dm).submatrix σ σ h k) := by
  rw [Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨σ.symm j, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    exact (fourier_column_eq e σ Dm h j).symm
  · rintro ⟨k, rfl⟩
    refine ⟨_, ⟨σ k, rfl⟩, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply]
    exact fourier_column_eq e σ Dm h (σ k)
end ReciprocityTheory.PGsh.L2
