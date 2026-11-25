-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:29:29.092662+00:00
-- url     : https://prove2.me/submissions/53b0526c-0c7a-4d0c-986a-bf3e0b629b64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_of_local
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__ne_zero_iff_2a770214a5a4
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__res_9bf5469fe96a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {T : Scheme.{0}} [IsAffine T] {B : Set V} (hB : IsOpen B) {z : V → (Sp ℂ ⟶ T)}
    (hz : ∀ r : Γ(T, ⊤), DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ r) B) : IsHolTo B z := by
  refine isHolTo_of_local fun U f b₀ hb₀ hU => ?_
  have hmem : (z b₀) cpt ∈ U := hU (Set.mem_univ _)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := U) ⟨(z b₀) cpt, hmem⟩ trivial
  have htop : ∀ b, ⊤ ≤ z b ⁻¹ᵁ (⊤ : T.Opens) := fun b p _ => trivial

  set N := {b ∈ B | valAt' (z b) ⊤ r ≠ 0} with hNdef
  have hNo : IsOpen N := (hz r).continuousOn.isOpen_inter_preimage hB isOpen_ne
  have hmemD : ∀ b, valAt' (z b) ⊤ r ≠ 0 → ⊤ ≤ z b ⁻¹ᵁ T.basicOpen r := fun b hb =>
    top_le_of_mem ((valAt'_ne_zero_iff (z b) ⊤ (htop b) r cpt).1 hb)
  have hb0N : b₀ ∈ N := ⟨hb₀, (valAt'_ne_zero_iff (z b₀) ⊤ (htop b₀) r cpt).2 hr0⟩

  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r)
    (T.presheaf.map (homOfLE hrU).op f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk
  have hval : ∀ b ∈ N, valAt' (z b) U f * valAt' (z b) ⊤ r ^ k = valAt' (z b) ⊤ hh := by
    intro b hb
    have hD := hmemD b hb.2
    have e := congrArg (valAt' (z b) (T.basicOpen r)) hk
    rw [valAt'_mul, valAt'_res (z b) hrU hD] at e
    have e2 : ∀ x : Γ(T, ⊤), valAt' (z b) (T.basicOpen r) (algebraMap Γ(T, ⊤) Γ(T, T.basicOpen r) x) =
        valAt' (z b) ⊤ x := fun x => valAt'_res (z b) le_top hD x
    rw [e2, e2, ← hks] at e
    have e3 : valAt' (z b) ⊤ (r ^ k) = valAt' (z b) ⊤ r ^ k := map_pow (valHom (z b) ⊤ (htop b)) r k
    rw [e3] at e
    exact e
  refine ⟨N, hNo.mem_nhds hb0N, fun b hb => ⟨hb.1, (hmemD b hb.2).trans (Scheme.Hom.preimage_mono _ hrU)⟩, ?_⟩
  have h1 : DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ hh) N := (hz hh).mono fun b (hb : b ∈ N) => hb.1
  have h2 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k) N :=
    ((hz r).mono fun b (hb : b ∈ N) => hb.1).pow k
  have h3 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k)⁻¹ N :=
    h2.inv fun b (hb : b ∈ N) => by simp only [Pi.pow_apply]; exact pow_ne_zero _ hb.2
  have h4 := h1.mul h3
  refine h4.congr fun b hb => ?_
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hb.2)]
  exact hval b hb
end ReciprocityTheory.ChartRestriction.G.PullbackSections
