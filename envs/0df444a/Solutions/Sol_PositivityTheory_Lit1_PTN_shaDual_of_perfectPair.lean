-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.shaDual_of_perfectPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:25.038916+00:00
-- url     : https://prove2.me/submissions/c7522fec-fdfe-4d70-a53b-ce7bff52b1c2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquivStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsShaHalf
import Theorems.Thm_PositivityTheory_Lit1_PTN_shaHalf_of_perfectPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution
    (h1 : PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
    (h2 : PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) : ShaDual S Av μ ρ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact ⟨shaHalf_of_perfectPair h1, shaHalf_of_perfectPair h2⟩
end PositivityTheory.Lit1.PTN
