-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.exists_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:34.287742+00:00
-- url     : https://prove2.me/submissions/25533f7c-5657-4b34-aa87-e6811001f5bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauPev_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sH_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_evP_sHp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_evalAtPoint_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)
include hd
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (P : Ω c →+* ℂ) (hP : P ∈ d.ST c sg (fun i j => pt (i.succ, j))) :
    ∃ σ : OmS (Ω c) d.D d.N →+* ℂ, σ.comp (d.KTtoS h c) = tauPev sg pt hpt ∧
      σ.comp (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) = P := by
  have hinj := d.evalAtPoint_injective hd h c sg pt hpt P hP
  refine ⟨IsFractionRing.lift (A := MvPolynomial (SVar d.D d.N) (Ω c)) (K := OmS (Ω c) d.D d.N) hinj,
    ?_, ?_⟩
  · apply IsLocalization.ringHom_ext (nonZeroDivisors (KTp K d.D d.N))
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply]
    rw [d.KTtoS_alg h c q, tauPev_apply, d.sH_eq c q, IsFractionRing.lift_algebraMap]
    exact d.evP_sHp c sg pt hd P hP.1 hP.2 q
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, ← d.algC c a, IsFractionRing.lift_algebraMap]
    simp [evP]
end ReciprocityTheory.ChartRestriction.G.T0.Data
