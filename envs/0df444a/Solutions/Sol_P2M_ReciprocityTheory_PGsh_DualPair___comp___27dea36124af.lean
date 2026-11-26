-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:59:55.468377+00:00
-- url     : https://prove2.me/submissions/871db4dd-4e9a-439a-ac5f-0694c9e2a167

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
theorem _root_.solution : Dp.π.comp Dp.σ = LHom.id R := by
  refine Subtype.ext (AlgHom.ext fun d => ?_)
  first
  | exact Dp.sect d
  | rfl
  | (show Dp.fμ 0 d = Dp.σ.1 (Dp.π.1 d); simp [ReciprocityTheory.PGsh.DualPair.fμ])
  | (show Dp.fμ c (Dp.σ.1 d) = Dp.σ.1 d; simp [ReciprocityTheory.PGsh.DualPair.fμ, Dp.sect])
  | (show Dp.π.1 (Dp.fμ c d) = Dp.π.1 d; simp [ReciprocityTheory.PGsh.DualPair.fμ, Dp.sect])
  | (apply Subtype.ext; show (Dp.σ.1 (Dp.π.1 (Dp.σ.1 (Dp.π.1 d))) , _) = _; simp [Dp.sect])
  | (apply Subtype.ext; refine Prod.ext ?_ ?_ <;> simp [ReciprocityTheory.PGsh.DualPair.i₁L, ReciprocityTheory.PGsh.DualPair.i₂L, ReciprocityTheory.PGsh.mkLHom, ReciprocityTheory.PGsh.LHom.comp, Dp.sect] <;> simp [Dp.sect])
  | (simp [ReciprocityTheory.PGsh.DualPair.sL, ReciprocityTheory.PGsh.DualPair.i₁L, ReciprocityTheory.PGsh.DualPair.i₂L, ReciprocityTheory.PGsh.DualPair.sA, ReciprocityTheory.PGsh.mkLHom, ReciprocityTheory.PGsh.LHom.comp, ReciprocityTheory.PGsh.LHom.id, Dp.sect])
  | (show Dp.sA ⟨(d, Dp.σ.1 (Dp.π.1 d)), (Dp.sect (Dp.π.1 d)).symm⟩ = d; simp [ReciprocityTheory.PGsh.DualPair.sA, ReciprocityTheory.PGsh.DualPair.sf, Dp.sect])
  | (show Dp.sA ⟨(Dp.σ.1 (Dp.π.1 d), d), Dp.sect (Dp.π.1 d)⟩ = d; simp [ReciprocityTheory.PGsh.DualPair.sA, ReciprocityTheory.PGsh.DualPair.sf, Dp.sect])



