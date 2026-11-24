-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerreFinite_proof_2527071963fc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:48.575897+00:00
-- url     : https://prove2.me/submissions/58f97dfb-58d9-476c-aaa8-dd53d98c16e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerreFinite
theorem _root_.solution (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _ i hi c
      have := hTop S N M 𝓜 i c (by omega)
      exact ⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM i hi c
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      have hF : Module.Finite S (cohom 𝓕 i c) := (hFree S N F 𝓕 r b d hb).1 i c
      have hKf : Module.Finite S (cohom 𝓚 (i + 1) c) := ih K 𝓚 hK (i + 1) (by omega) c
      obtain ⟨-, δ, hδ, -⟩ := (hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
      rw [top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]
      exact hF.fg_top.map _
  intro M _ _ _ _ 𝓜 hM i c
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  have := key (N + 1) M' 𝓜' hM' i (by omega) c
  exact Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)
end SerreFinite
end GroundTheory.Heights₂.Heights.Kleiman
