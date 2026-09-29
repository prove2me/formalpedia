-- Prove2me | solution 1 for QFS.lemma_appendixA_alpha_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-07T08:39:42.130186+00:00
-- url     : https://prove2.me/submissions/1dbbaa6f-8ebe-4f86-8f34-3976fdefb241

import Theorems.Thm_QFS_formHs_le_form_domain
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_FavoredGraph
import Definitions.Def_QFS_Indicator
import Definitions.Def_QFS_WhitneyDomain
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Appendix A: the auxiliary lemmas

The paper's `\appendix` prints as Appendix A, with Lemmas A.1 and A.2.

**The chain (18) inside Lemma A.1.** Lemma A.1 passes from balls to a bounded
Lipschitz domain using a Whitney family and Dyda's inequality (13), both quoted
rather than proved. The one step the paper carries out itself is the
finite-overlap estimate, and it is proved here
(`tsum_setLIntegral_le_of_overlap`); `lemma_ball_to_domain` then assembles the
whole chain with the two quoted inputs as explicit hypotheses.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}

theorem solution {κ c₀ α₀ γ : ℝ} {M : ℕ} (hc₀ : 1 ≤ c₀)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (W : ∀ α, α₀ ≤ α → α < 2 → WhitneyDomainData d α κ Ω)
    (hM : ∀ α h₁ h₂, (W α h₁ h₂).overlapBound = M)
    (hγ : ∀ α h₁ h₂, (W α h₁ h₂).dydaConst = γ)
    (H : ∀ α, α₀ ≤ α → α < 2 → ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∀ α, α₀ ≤ α → α < 2 →
      ENNReal.ofReal (c₀⁻¹ * γ / (M : ℝ)) * formHs Ω α f ≤ form Ω k f := by
  intro α h₁ h₂
  have := QFS.formHs_le_form_domain hc₀ hΩ (W α h₁ h₂) (H α h₁ h₂) hf hFmeas
  rwa [hM α h₁ h₂, hγ α h₁ h₂] at this
