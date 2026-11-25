-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.blkLat_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:06.461691+00:00
-- url     : https://prove2.me/submissions/74872529-b6a9-49cf-9d70-2fe83d57754e

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : (blkLat Ls).pts = sumPts Ls := by
  have hmv : ∀ c : Fin n × Fin s → C, (blkLat Ls).B *ᵥ c =
      fun y => ((Ls y.1).B *ᵥ fun j => c (y.1, j)) y.2 := by
    intro c
    ext ⟨τ, i⟩
    simp only [blkLat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul]
    rw [Finset.sum_eq_single τ]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  ext w
  simp only [ReciprocityTheory.PGsh.Lat.pts, sumPts, Set.mem_setOf_eq, hmv]
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    exact ⟨fun j => c (τ, j), fun j => hc (τ, j), rfl⟩
  · intro hw
    choose c hc hce using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext y
    exact congrFun (hce y.1) y.2
end ReciprocityTheory.PGsh.Up
