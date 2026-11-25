-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_cartAt_e59396769268
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:48.893445+00:00
-- url     : https://prove2.me/submissions/adddc098-aaad-4fd6-a082-62dcc71ff171

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmoothStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPairStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_fromSpec_mem_basicOpen_iff_8be40fd86d42
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602
import Theorems.Thm_GlobalTheory_T_cartier_at_of_locally_principal
import Theorems.Thm_GlobalTheory_T_exists_smooth_affine_presentation_pair
import Theorems.Thm_GlobalTheory_T_locally_principal_of_cartier_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  intro k _ X g Z hg hX hZ
  have key : ∀ x ∈ (Z.support : Set X), ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ (Z.support : Set X) → (CartAt Z y ↔ CartAt Z x) := by
    intro x hx
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    let U' : X.affineOpens := ⟨U, hU⟩
    have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hdom : IsDomain Γ(X, U'.1) := inferInstanceAs (IsDomain Γ(X, U))
    obtain ⟨φ, hφ, hI⟩ := GlobalTheory.T.exists_smooth_affine_presentation_pair g Z U' hg hZ
    have hrange : ∀ y ∈ U, ∃ q, U'.2.fromSpec q = y := by
      intro y hy
      have : y ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hy
      exact this
    have hIq : ∀ q : PrimeSpectrum Γ(X, U'.1), U'.2.fromSpec q ∈ (Z.support : Set X) →
        Z.ideal U' ≤ q.asIdeal := by
      intro q hq f hf
      by_contra hfq
      have hb := (fromSpec_mem_basicOpen_iff U' q f).2 hfq
      have hmem : U'.2.fromSpec q ∈ (Z.support : Set X) ∩ (U'.1 : Set X) :=
        ⟨hq, X.basicOpen_le f hb⟩
      rw [Z.coe_support_inter U'] at hmem
      exact (Scheme.mem_zeroLocus_iff _ _ _).1 hmem.1 f hf hb
    obtain ⟨q0, rfl⟩ := hrange x hxU
    obtain ⟨s, hs, h⟩ := locPrincipal_locally_const φ (Z.ideal U') hφ hI q0 (hIq q0 hx)
    refine ⟨X.basicOpen s, (X.basicOpen s).isOpen, (fromSpec_mem_basicOpen_iff U' q0 s).2 hs, ?_⟩
    intro y hy hyZ
    obtain ⟨q, rfl⟩ := hrange y (X.basicOpen_le s hy)
    have := h q ((fromSpec_mem_basicOpen_iff U' q s).1 hy) (hIq q hyZ)
    exact ⟨fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q0 (this.1 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q hc)),
      fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q (this.2 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q0 hc))⟩
  have hC : IsClosed (Z.support : Set X) := Z.support.isClosed
  refine ⟨isClosed_of_locally_iff hC _ key, isClosed_of_locally_iff hC _ fun x hx => ?_⟩
  obtain ⟨V, hV, hxV, hy⟩ := key x hx
  exact ⟨V, hV, hxV, fun y hyV hyC => not_congr (hy y hyV hyC)⟩
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
