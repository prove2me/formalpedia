-- Prove2me | solution 1 for P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:00:07.494493+00:00
-- url     : https://prove2.me/submissions/1f63c50f-6aa3-43f2-9a5e-85c65c84f2c1

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_ContinuousLinearMapRank

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
namespace SNumbers
theorem _root_.solution (n : ℕ) :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by
  rw [(WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).finrank_eq, Module.finrank_pi 𝕜]
  exact Fintype.card_fin _
end SNumbers
