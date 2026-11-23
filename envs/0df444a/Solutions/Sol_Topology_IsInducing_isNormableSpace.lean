-- Prove2me | solution 1 for Topology.IsInducing.isNormableSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:05.282707+00:00
-- url     : https://prove2.me/submissions/cee2147c-c29d-402d-8b32-804461695b75

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability

set_option autoImplicit true
open Topology
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
namespace Topology.IsInducing
theorem _root_.solution [h : IsNormableSpace 𝕜 F]
    [TopologicalSpace E] {f : E →ₗ[𝕜] F} (hf : IsInducing f) :
    IsNormableSpace 𝕜 E := by
  rcases h.withSeminorms' with ⟨p, hp⟩
  exact ⟨p.comp f, hf.withSeminorms hp⟩
end Topology.IsInducing
