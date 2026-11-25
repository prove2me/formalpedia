-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:48.035594+00:00
-- url     : https://prove2.me/submissions/66a3151d-690a-45e2-98de-e3f2ecb92839

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_zOf_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_zOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_sep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_exists_implicit_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_deh
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_differentiableAt_eval__deh_073b6e6e1812

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution (hx0 : x (e 0) ≠ 0) {W : Set (Fin (D + 1) → ℂ)} (hWo : IsOpen W)
    (hgood : ∀ w ∈ W, G.Good w) {w : Fin (D + 1) → ℂ} (hw : w ∈ W) {z : ι → ℂ}
    (hz : z ∈ fib x e w) :
    ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → ι → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ fib x e w' := by
  have hgw := hgood w hw
  obtain ⟨hroot, hzeq⟩ := G.of_mem hx0 hgw hz.1 hz.2
  generalize hρ : deh z (e 0) G.Θ = ρ at hroot hzeq
  have hp1 : ∀ i, ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1 i) (w, ρ) := by
    intro i
    first
    | fun_prop
    | exact ((contDiff_apply ℂ ℂ i).comp contDiff_fst).contDiffAt
    | exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) i).comp
        (ContinuousLinearMap.fst ℂ (Fin (D + 1) → ℂ) ℂ)).contDiff.contDiffAt
  have hcd : ContDiffAt ℂ 1 (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) :=
    contDiffAt_eval₂_deh (fun p : (Fin (D + 1) → ℂ) × ℂ => p.1) (fun p => p.2) (w, ρ) 0 hp1
      contDiffAt_snd hgw.w0 G.P
  have hd0 := (G.P.map (deh w 0)).hasDerivAt ρ
  simp only [Polynomial.eval_map] at hd0
  have hsep := G.sep hgw
  rw [Polynomial.separable_def] at hsep
  obtain ⟨a, b, hab⟩ := hsep
  have hev := congrArg (Polynomial.eval ρ) hab
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_map, hroot, mul_zero, zero_add] at hev
  have hc : Polynomial.eval ρ (Polynomial.derivative (G.P.map (deh w 0))) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hev
    exact zero_ne_one hev
  obtain ⟨U', τ, hU'o, hwU', hτd, hτw, hτf⟩ :=
    exists_implicit_section (fun p : (Fin (D + 1) → ℂ) × ℂ => G.P.eval₂ (deh p.1 0) p.2) (w, ρ) hcd hc hd0
  have hτw' : τ w = ρ := hτw
  have hproj : ∀ (v : Fin (D + 1) → ℂ) j, ContDiffAt ℂ 1 (fun u : Fin (D + 1) → ℂ => u j) v := by
    intro v j
    first
    | fun_prop
    | exact (contDiff_apply ℂ ℂ j).contDiffAt
    | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) j).contDiff.contDiffAt
  refine ⟨U' ∩ W, fun w' => G.zOf w' (τ w'), hU'o.inter hWo, ⟨hwU', hw⟩, ?_, ?_, ?_⟩
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hτa : DifferentiableAt ℂ τ w' := hτd.differentiableAt (hU'o.mem_nhds hw'.1)
    apply DifferentiableAt.differentiableWithinAt
    rw [differentiableAt_pi]
    intro i
    have hA := differentiableAt_eval₂_deh (fun u => u) τ w' 0 (hproj w') hτa hg'.w0 (G.Q i)
    have hB := (contDiffAt_deh (fun u => u) w' 0 (hproj w') hg'.w0 G.dd).differentiableAt one_ne_zero
    have hC := hA.mul (hB.inv hg'.dd)
    simp only [Gen.zOf, Gen.evQ, div_eq_mul_inv]
    exact ((hproj w' 0).differentiableAt one_ne_zero).mul hC
  · show G.zOf w (τ w) = z
    rw [hτw']
    exact hzeq
  · intro w' hw'
    have hg' := hgood w' hw'.2
    have hr : G.P.eval₂ (deh w' 0) (τ w') = 0 := (hτf w' hw'.1).trans hroot
    exact ⟨G.zOf_mem hx0 hg' hr, G.zOf_e hg' hr⟩
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
