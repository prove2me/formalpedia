-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2.lagrange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:58.414744+00:00
-- url     : https://prove2.me/submissions/94de6b47-707b-4a7a-8969-53f37548173b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_ExpChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2
theorem _root_.solution (C : Finset ℂ) (c : ℂ) : ∃ (τs : Finset ℝ) (a : ℝ → ℂ), ∀ c' ∈ C,
    ∑ t ∈ τs, a t * Complex.exp (c' * t) = if c' = c then 1 else 0 := by
  classical
  have expChar_injective : Function.Injective expChar := by
    intro c c' h
    have hd : ∀ d : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (d * (t : ℂ))) d 0 := by
      intro d
      have h1 : HasDerivAt (fun t : ℝ => d * (t : ℂ)) (d * 1) 0 :=
        ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul d
      have h2 := h1.cexp
      simpa using h2
    have hf : (fun t : ℝ => Complex.exp (c * (t : ℂ))) = fun t : ℝ => Complex.exp (c' * (t : ℂ)) := by
      funext t
      have := DFunLike.congr_fun h (Multiplicative.ofAdd t)
      simpa [expChar] using this
    have e := hd c
    rw [hf] at e
    exact e.unique (hd c')
  let v : ℝ → (C → ℂ) := fun t c' => Complex.exp ((c' : ℂ) * t)
  have hli : LinearIndependent ℂ (fun c' : C => (expChar (c' : ℂ) : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp (fun c' : C => expChar (c' : ℂ))
      (expChar_injective.comp Subtype.val_injective)
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hw : ∀ i : C, f (Pi.single i 1) = 0 := by
      have hsum : ∑ i : C, f (Pi.single i 1) • (expChar (i : ℂ) : Multiplicative ℝ → ℂ) = 0 := by
        funext x
        have hx : f (v (Multiplicative.toAdd x)) = 0 := hle (Submodule.subset_span ⟨_, rfl⟩)
        have hv : v (Multiplicative.toAdd x) = ∑ i : C, (v (Multiplicative.toAdd x) i) • Pi.single i 1 := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        rw [hv, map_sum] at hx
        simp only [map_smul, smul_eq_mul] at hx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hx]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [expChar, v, mul_comm]
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hsum i
    exact (Pi.basisFun ℂ C).ext fun i => by simpa using hw i
  have hmem : (fun c' : C => if (c' : ℂ) = c then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range v) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨a.support, a, fun c' hc' => ?_⟩
  have := congrFun ha ⟨c', hc'⟩
  rw [Finsupp.sum, Finset.sum_apply] at this
  simpa [v] using this
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2
