-- Prove2me | solution 1 for RiemannMasullo.regulator_eq_infiniteIdeleLog
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:32:49.845758+00:00
-- url     : https://prove2.me/submissions/054cf963-91a7-4af2-abb7-f789755ab806

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L127-L129
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
open NumberField.Units.dirichletUnitTheorem
local notation "unitAtInfinity" => Units.map (RingHom.toMonoidHom
  (RingHom.comp (algebraMap F (InfiniteAdeleRing F)) (algebraMap (𝓞 F) F)))

theorem solution (u : (𝓞 F)ˣ) (v : {w : InfinitePlace F // w ≠ w₀}) :
    Units.logEmbedding F (Additive.ofMul u) v = infiniteIdeleLog F (unitAtInfinity u) v.val := by
  rw [logEmbedding_component]
  unfold infiniteIdeleLog
  congr 2
  exact (InfinitePlace.Completion.norm_coe v.val
    ((WithAbs.equiv v.val.1).symm (algebraMap (𝓞 F) F u.val))).symm
