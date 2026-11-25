-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal.dimPIT_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:50.377748+00:00
-- url     : https://prove2.me/submissions/6ceb586a-2412-4f7e-913a-5e76abbb0949

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_RingKrullDimQuotientAddOneLeOfLt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_DimFormulaOfSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_ringKrullDim_quotient_ne_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_isCM_atPrime_of_le
import Theorems.Thm_ReciprocityTheory_CA_dimFormula_arith
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_CA_height_eq_add_of_isCM_localization
import Theorems.Thm_ReciprocityTheory_CA_height_maximal_mvPolynomial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
open ReciprocityTheory.CA
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
theorem _root_.solution (F : Type) [Field F] (N : ℕ) (V W : Ideal (MvPolynomial (Fin N) F))
    (s : MvPolynomial (Fin N) F) (hV : V.IsPrime) (hs : s ∉ V)
    (hW : W ∈ (V ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) F ⧸ W) + 1 =
      ringKrullDim (MvPolynomial (Fin N) F ⧸ V) := by
  have hWp : W.IsPrime := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨𝔐, h𝔐, hW𝔐⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have hCM := (height_maximal_mvPolynomial_field F N 𝔐).1
  have hCMW := isCM_atPrime_of_le 𝔐 W hCM hW𝔐
  have hrel := height_eq_add_of_isCM_localization W V hCMW hVW
  let f := Ideal.Quotient.mk V
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ W := by rw [Ideal.mk_ker]; exact hVW
  have hP : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hcomapJ : (Ideal.span {f s}).comap f = V ⊔ Ideal.span {s} := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hf,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  have hmin : W.map f ∈ (Ideal.span {f s}).minimalPrimes := by
    have h0 := hW
    rw [← hcomapJ, Ideal.comap_minimalPrimes_eq_of_surjective hf] at h0
    obtain ⟨Q, hQ, hQW⟩ := h0
    rw [← hQW, Ideal.map_comap_of_surjective _ hf]
    exact hQ
  have : (Ideal.span {f s}).IsPrincipal := ⟨⟨f s, rfl⟩⟩
  have hle1 : (W.map f).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : W.map f ≠ ⊥ := by
    intro h0
    have h3 : f s ∈ W.map f := Ideal.mem_map_of_mem f hsW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
    exact hs h3
  have hge1 : 1 ≤ (W.map f).height := by
    rw [Order.one_le_iff_ne_zero]
    exact fun h0 => hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have h1 : (W.map f).height = 1 := le_antisymm hle1 hge1
  have eV := height_add_ringKrullDim_quotient_mvPolynomial_field F N V
  have eW := height_add_ringKrullDim_quotient_mvPolynomial_field F N W
  rw [hrel, h1] at eW
  have := dimFormula_arith V.height 1 _ _ N (ringKrullDim_quotient_ne_bot W hWp.ne_top)
    (ringKrullDim_quotient_ne_bot V hV.ne_top) eW eV
  rw [add_comm]
  exact_mod_cast this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
