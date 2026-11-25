-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.exists_integral_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:15.050883+00:00
-- url     : https://prove2.me/submissions/26e80d0c-4b45-4269-89b7-b1fbf069c32e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_w_eq_scalarRatio_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_valuationRing


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
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) :
    ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing v) ∧
      ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 ∧
      ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dif_pos hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have key : ∀ a b : WithTop ℤ, b ≠ ⊤ → b ≤ a + b → 0 ≤ a := by
    intro a b hb h
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top => exact absurd rfl hb
      | coe b =>
        have h1 : (b : WithTop ℤ) ≤ ((a + b : ℤ) : WithTop ℤ) := by exact_mod_cast h
        have h2 : b ≤ a + b := WithTop.coe_le_coe.mp h1
        exact_mod_cast (show (0 : ℤ) ≤ a by omega)
  have smul_ne : ∀ (a : Ω c) (g : A c), a ≠ 0 → g ≠ 0 → a • g ≠ 0 := by
    intro a g ha hg h
    apply hg
    have h1 := congrArg (fun y => a⁻¹ • y) h
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ ha] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => v (q j)) ⟨d.jc c, Finset.mem_univ _⟩
  have hvle : v (q j0) ≤ 0 := by
    have h1 := hj0 (d.jc c) (Finset.mem_univ _)
    rwa [hq1, AddValuation.map_one] at h1
  have hq0 : q j0 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hvle
    first
    | exact absurd hvle (by simp)
    | exact WithTop.zero_ne_top (top_le_iff.mp hvle)
  have hw0 : d.w j0 c ≠ 0 := by
    rw [hx j0]
    exact smul_ne _ _ hq0 (hd.w_base c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) = q j / q j0 := by
    intro j
    apply uniq _ _ _ hw0
    rw [hx j, hx j0, smul_smul, div_mul_cancel₀ _ hq0]
  refine ⟨j0, hw0, fun j => ?_, by rw [hqdef]; exact hq0, fun j => by rw [hrat j, hqdef, hqdef]⟩
  rw [mem_valuationRing, hrat j]
  have hmul : v (q j) = v (q j / q j0) + v (q j0) := by
    rw [← AddValuation.map_mul, div_mul_cancel₀ _ hq0]
  have hle := hj0 j (Finset.mem_univ _)
  rw [hmul] at hle
  have hnt : v (q j0) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact hq0 h
  exact key _ _ hnt hle
end ReciprocityTheory.ChartRestriction.G.T0.Data
