-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral.Ich_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:54.268697+00:00
-- url     : https://prove2.me/submissions/2935380c-44a4-458b-a2b1-d8a06e21f8de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeIntegral_cube_int_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Bv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Bv_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_ech_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_ech_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
  MeasureTheory Set Filter
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {u : Fin 2 → Fin r → E} {g : ℕ} {ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
  {G : Frame X.Ψ r → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
theorem _root_.solution (hω : X.IsLZBasis g ω)
    (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
    (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (hG : DifferentiableOn ℂ G X.dom) (hper : ∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x)
    {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k)
    {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Ich X u ω G χ (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * Ich X u ω G χ x := by
  have hωh : ∀ j, IsHermFam (ω j) := by
    intro j τ i k
    obtain ⟨β, hβ, -, hb⟩ := hω.1 j
    rw [hb]
    simp only [Data.embH]
    rw [← hβ i k, cc, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨s, hs⟩ : ∃ s : Fin (4 * Fintype.card X.Ψ) → ℝ, Bv ω s = b := by
    let H : Submodule ℝ (X.Ψ → Fin 2 → Fin 2 → ℂ) :=
      { carrier := {b | IsHermFam b}
        add_mem' := fun {a c} ha hc τ i k => by
          simp only [Pi.add_apply, map_add]
          rw [ha τ i k, hc τ i k]
        zero_mem' := fun τ i k => by simp
        smul_mem' := fun r a ha τ i k => by
          simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
          rw [ha τ i k] }
    have hωH : ∀ j, ω j ∈ H := hωh
    let f : (X.Ψ → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (X.Ψ → Fin 4 → ℝ) :=
      { toFun := fun b τ => ![(b τ 0 0).re, (b τ 1 1).re, (b τ 0 1).re, (b τ 0 1).im]
        map_add' := fun a c => by
          funext τ m
          fin_cases m <;> simp
        map_smul' := fun r a => by
          funext τ m
          fin_cases m <;> simp }
    have hinj : Function.Injective (f.comp H.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have hh : IsHermFam (a : X.Ψ → Fin 2 → Fin 2 → ℂ) := a.2
      apply Subtype.ext
      funext τ i k
      show (a : X.Ψ → Fin 2 → Fin 2 → ℂ) τ i k = 0
      have e := fun m => congrFun (congrFun ha τ) m
      have e0 : (a.1 τ 0 0).re = 0 := by simpa [f] using e 0
      have e1 : (a.1 τ 1 1).re = 0 := by simpa [f] using e 1
      have e2 : (a.1 τ 0 1).re = 0 := by simpa [f] using e 2
      have e3 : (a.1 τ 0 1).im = 0 := by simpa [f] using e 3
      have i00 : (a.1 τ 0 0).im = 0 := by
        have h := congrArg Complex.im (hh τ 0 0)
        rw [Complex.conj_im] at h
        linarith
      have i11 : (a.1 τ 1 1).im = 0 := by
        have h := congrArg Complex.im (hh τ 1 1)
        rw [Complex.conj_im] at h
        linarith
      have z00 : a.1 τ 0 0 = 0 := Complex.ext (by simpa using e0) (by simpa using i00)
      have z11 : a.1 τ 1 1 = 0 := Complex.ext (by simpa using e1) (by simpa using i11)
      have z01 : a.1 τ 0 1 = 0 := Complex.ext (by simpa using e2) (by simpa using e3)
      have z10 : a.1 τ 1 0 = 0 := by rw [hh τ 0 1, z01, map_zero]
      fin_cases i <;> fin_cases k
      · exact z00
      · exact z01
      · exact z10
      · exact z11
    have hH : Module.finrank ℝ H ≤ 4 * Fintype.card X.Ψ := by
      have h := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [Module.finrank_pi_fintype, Module.finrank_fin_fun, Finset.sum_const, mul_comm] using h
    have hspan : Submodule.span ℝ (Set.range ω) = H := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact Submodule.span_le.2 (Set.range_subset_iff.2 hωH)
      · rw [finrank_span_eq_card hω.2.2, Fintype.card_fin]
        exact hH
    have hbH : b ∈ H := hb
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hbH
    obtain ⟨c, hc⟩ := hbH
    refine ⟨c, ?_⟩
    rw [← hc]
    funext τ i k
    simp [Bv, Finset.sum_apply, Complex.real_smul]
  subst hs
  choose k hk using hfreq
  have hLZ : ∀ n : Fin (4 * Fintype.card X.Ψ) → ℤ, Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
    intro n
    have hsum : ∀ S : Finset (Fin (4 * Fintype.card X.Ψ)),
        ∑ j ∈ S, ((n j : ℝ) : ℂ) • ω j ∈ X.LZ g := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        refine ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩, ?_⟩
        funext τ i k
        simp [Data.embH]
      | insert j S hj ih =>
        rw [Finset.sum_insert hj]
        obtain ⟨β, hβ, hint, hb⟩ := hω.1 j
        obtain ⟨β', hβ', hint', hb'⟩ := ih
        simp only [cc] at hβ hβ'
        refine ⟨(n j : E) • β + β', fun i k => ?_, fun i k => ?_, ?_⟩
        · simp [cc, hβ, hβ', map_add, map_mul, map_intCast]
        · obtain ⟨γ, hγ, hγe⟩ := hint i k
          obtain ⟨γ', hγ', hγe'⟩ := hint' i k
          have hn : IsIntegral ℤ (n j : E) := by
            simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := n j)
          refine ⟨(n j : E) * γ + γ', (hn.mul hγ).add hγ', ?_⟩
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hγe, hγe']
          ring
        · rw [hb, hb']
          funext τ i k
          simp [Data.embH, map_add, map_mul, map_intCast]
    exact hsum Finset.univ
  have hZc : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => X.Zb u (Bv ω t) x := by
    refine continuous_pi fun τ => ?_
    show Continuous fun t => X.zmat u (Bv ω t) τ * mat x τ
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_pi fun a => continuous_pi fun j => ?_
    simp only [Data.zmat, Matrix.of_apply, Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hec : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => ech ω χ t := by
    simp only [ech, pr, Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hcont : Continuous fun t : Fin (4 * Fintype.card X.Ψ) → ℝ => G (X.Zb u (Bv ω t) x) * ech ω χ t :=
    (hG.continuousOn.comp_continuous hZc fun t => hdomH _ (Bv_herm ω hωh t) x hx).mul hec
  have hF : ∀ (n : Fin (4 * Fintype.card X.Ψ) → ℤ) (t : Fin (4 * Fintype.card X.Ψ) → ℝ),
      (fun t => G (X.Zb u (Bv ω t) x) * ech ω χ t) (t + fun i => (n i : ℝ)) =
        (fun t => G (X.Zb u (Bv ω t) x) * ech ω χ t) t := by
    intro n t
    show G (X.Zb u (Bv ω (t + fun i => (n i : ℝ))) x) * ech ω χ (t + fun i => (n i : ℝ)) =
      G (X.Zb u (Bv ω t) x) * ech ω χ t
    rw [Bv_add, add_comm (Bv ω t), ← hadd, hper _ (hLZ n) _ (hdomH _ (Bv_herm ω hωh t) x hx),
      ech_add, ech_int (ω := ω) χ hk n, mul_one]
  have hshift := cube_int_shift _ hcont hF s
  have hinv : ech ω χ s * cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) = 1 := by
    show cexp (-(4 * Real.pi * I) * (X.pairR χ (Bv ω s) : ℂ)) *
      cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) = 1
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  have hpt : ∀ t, G (X.Zb u (Bv ω t) (X.Zb u (Bv ω s) x)) * ech ω χ t =
      (G (X.Zb u (Bv ω (t + s)) x) * ech ω χ (t + s)) *
        cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) := by
    intro t
    rw [hadd, ← Bv_add, ech_add, mul_assoc, mul_assoc, hinv, mul_one]
  show ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) (X.Zb u (Bv ω s) x)) * ech ω χ t =
    cexp (4 * Real.pi * I * X.pairR χ (Bv ω s)) *
      ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t
  simp_rw [hpt]
  rw [integral_mul_const, hshift, mul_comm]
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeIntegral
