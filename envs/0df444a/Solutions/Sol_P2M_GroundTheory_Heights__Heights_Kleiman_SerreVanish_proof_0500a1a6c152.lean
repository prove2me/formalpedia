-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerreVanish_proof_0500a1a6c152
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:02.403805+00:00
-- url     : https://prove2.me/submissions/5b6df9d5-b12e-4551-97f4-c7f011de53ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreVanish

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
namespace SerreVanish
theorem _root_.solution (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreVanish.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∃ c₀ : ℤ, ∀ i, N + 1 ≤ i + k → 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _
      exact ⟨0, fun i hi _ c _ => hTop S N M 𝓜 i c (by omega)⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      obtain ⟨c₁, hc₁⟩ := ih K 𝓚 hK
      refine ⟨max c₁ (∑ j, |d j|), fun i hi hi1 c hc => ?_⟩
      have hdc : ∀ j, d j ≤ c := fun j =>
        ((le_abs_self (d j)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (d j))
          (Finset.mem_univ j))).trans ((le_max_right _ _).trans hc)
      have hF := ((hFree S N F 𝓕 r b d hb).2 c hdc).1 i hi1
      have hKv := hc₁ (i + 1) (by omega) (by omega) c ((le_max_left _ _).trans hc)
      obtain ⟨δ, hδ, -⟩ := ((hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i).2
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : cohom 𝓜 i c, z = 0 := fun z => by
        obtain ⟨w, hw⟩ := (hδ z).mp (Subsingleton.elim _ _)
        rw [← hw, Subsingleton.elim w 0, map_zero]
      rw [hx x, hx y]
  intro M _ _ _ _ 𝓜 hM
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  obtain ⟨c₀, hc₀⟩ := key N M' 𝓜' hM'
  refine ⟨c₀, fun i hi c hc => ?_⟩
  have := hc₀ i (by omega) hi c hc
  exact (hRet S N M M' 𝓜 𝓜' f g hgf i c).subsingleton
end SerreVanish
end GroundTheory.Heights₂.Heights.Kleiman
