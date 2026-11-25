-- Prove2me | solution 1 for PI.SqPair.LCP.pgen_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:27.589589+00:00
-- url     : https://prove2.me/submissions/5d1b6981-0679-4937-92b3-cf03106ac86e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
import Theorems.Thm_PI_SqPair_LCP_assemble
import Theorems.Thm_PI_SqPair_LCP_blk_unimod
import Theorems.Thm_PI_SqPair_LCP_blk_rel
import Theorems.Thm_PI_SqPair_LCP_phyp_reindex
import Theorems.Thm_PI_SqPair_LCP_isBase_reindex
import Theorems.Thm_PI_SqPair_LCP_pconcl_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution (hB : BaseLag) (hS : Step) {R : Type} [CommRing R] [StarRing R]
    (R₀ : Subring R) [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)] (ϖ : R)
    (hI : Inert R₀ ϖ) (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → Even n → PGen ϖ ι := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hc hev A A' h k hP
  by_cases hb : IsBase ϖ h k
  · obtain ⟨h₁, hh₁, rfl⟩ := hb
    obtain ⟨e, he, heA⟩ := hB R R₀ ϖ hI ι (hc ▸ hev) A hP.1
    refine ⟨e, h₁⁻¹ * e * h₁, he, heA, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc, mul_nonsing_inv h₁ hh₁, Matrix.one_mul]
  · match n, ih, hc, hev with
    | 0, _, hc, _ =>
      have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
      exact absurd ⟨1, by simp, by ext i; exact isEmptyElim i⟩ hb
    | 1, _, _, hev => exact absurd hev (by decide)
    | m + 2, ih, hc, hev =>
      let s : Fin 2 ⊕ Fin m ≃ ι := Fintype.equivOfCardEq (by simp [hc]; omega)
      apply pconcl_reindex s
      have hP' := phyp_reindex s hP
      have hb' : ¬ IsBase ϖ (h.submatrix s s) k := fun hb' => hb (isBase_reindex s hb')
      obtain ⟨u, u', A₁, A₁', h₂, d, hu, hu', hA, hA', hh⟩ := hS R R₀ ϖ hI (Fin m) _ _ _ k hP' hb'
      have hU₁ := blk_unimod hu hP'.1 hA
      have hU₁' := blk_unimod hu' hP'.2.1 hA'
      have hr := blk_rel ϖ k _ _ _ u u' A₁ A₁' h₂ d hP'.2.2 hA hA' hh
      have hevm : Even m := by
        obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩
      obtain ⟨e₂, f₂, he, heA, hef⟩ :=
        ih m (by omega) (Fin m) (Fintype.card_fin m) hevm A₁ A₁' h₂ k ⟨hU₁, hU₁', hr⟩
      exact assemble _ _ u u' A₁ h₂ d hu hu' hA hh e₂ f₂ he heA hef
end PI.SqPair.LCP
