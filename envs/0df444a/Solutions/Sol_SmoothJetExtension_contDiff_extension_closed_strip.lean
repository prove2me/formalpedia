-- Prove2me | solution 1 for SmoothJetExtension.contDiff_extension_closed_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:32:39.678163+00:00
-- url     : https://prove2.me/submissions/452a182a-f3ac-41a6-9828-e49b31418c5e

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace



open Set Filter
open scoped ContDiff Topology
namespace SmoothJetExtension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth function on a closed uniquely differentiable set with zero full jet
on its boundary extends smoothly by zero. This handles the endpoint gluing
needed for an isotopy given only on the closed time interval. -/
lemma contDiff_zero_extension_of_flat (S : Set E) (hS : IsClosed S)
    (hU : UniqueDiffOn ℝ S) (f : E → F) (hf : ContDiffOn ℝ ∞ f S)
    (hflat : ∀ x ∈ frontier S, ∀ n : ℕ, iteratedFDerivWithin ℝ n f S x = 0) :
    ContDiff ℝ ∞ (S.indicator f) := by
  classical
  let P := ftaylorSeriesWithin ℝ f S
  have hP : HasFTaylorSeriesUpToOn ∞ f P S := hf.ftaylorSeriesWithin hU
  let Q : E → FormalMultilinearSeries ℝ E F := fun x n => if x ∈ S then P x n else 0
  have hflatP : ∀ x ∈ frontier S, ∀ n : ℕ, P x n = 0 := hflat
  have hcz (n : ℕ) :
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) F).curryLeft = 0 := by
    ext v m; rfl
  have hderiv : ∀ n : ℕ, ∀ x : E,
      HasFDerivAt (fun y => Q y n) (Q x (n + 1)).curryLeft x := by
    intro n x
    by_cases hx : x ∈ S
    · by_cases hi : x ∈ interior S
      · have hd := (hP.fderivWithin n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x hx).hasFDerivAt (mem_interior_iff_mem_nhds.mp hi)
        have he : (fun y => Q y n) =ᶠ[𝓝 x] (fun y => P y n) := by
          filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
          simp only [Q, if_pos hy]
        simpa only [Q, if_pos hx] using hd.congr_of_eventuallyEq he
      · have hbd : x ∈ frontier S := by
          rw [frontier, hS.closure_eq]
          exact ⟨hx, hi⟩
        have hq0 : Q x n = 0 := by simp only [Q, if_pos hx, hflatP x hbd n]
        have hq1 : Q x (n + 1) = 0 := by simp only [Q, if_pos hx, hflatP x hbd (n + 1)]
        have hdS : HasFDerivWithinAt (𝕜 := ℝ) (fun y => Q y n) 0 S x := by
          have he := (hP.fderivWithin n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x hx).congr (f₁ := fun y => Q y n)
            (fun y hy => by simp only [Q, if_pos hy]) (by simp only [Q, if_pos hx])
          simpa only [hflatP x hbd (n + 1), hcz] using he
        have hdC : HasFDerivWithinAt (𝕜 := ℝ) (fun y => Q y n) 0 Sᶜ x := by
          apply (hasFDerivWithinAt_const (c := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F))
            (𝕜 := ℝ) (s := Sᶜ) (x := x)).congr
          · intro y hy
            simp only [Q, if_neg hy]
          · exact hq0
        rw [hq1]
        simpa only [hcz] using
          (hdS.union hdC).hasFDerivAt (by simp)
    · have he : (fun y => Q y n) =ᶠ[𝓝 x] (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)) := by
        filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy
        simp only [Q, if_neg hy]
      simpa only [Q, if_neg hx, hcz] using
        (hasFDerivAt_const (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) x).congr_of_eventuallyEq he
  have hT : HasFTaylorSeriesUpToOn ∞ (fun x => if x ∈ S then f x else 0) Q univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro x _
      by_cases hx : x ∈ S
      · simpa only [Q, if_pos hx] using hP.zero_eq x hx
      · simp only [Q, if_neg hx, ContinuousMultilinearMap.curry0_apply, ContinuousMultilinearMap.zero_apply]
    · intro n _ x _
      exact (hderiv n x).hasFDerivWithinAt
    · intro n _
      exact (continuous_iff_continuousAt.mpr fun x => (hderiv n x).continuousAt).continuousOn
  have he : S.indicator f = (fun x => if x ∈ S then f x else 0) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  exact contDiffOn_univ.mp hT.contDiffOn

end SmoothJetExtension

namespace SmoothJetExtension
open Set
open scoped ContDiff

lemma exists_contDiff_extension_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ∞ f {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → f p = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ ∞ H ∧
      EqOn H f {p : E × ℝ | 0 ≤ p.2} := by
  classical
  let S : Set (E × ℝ) := univ ×ˢ Ici (0 : ℝ)
  have hSeq : S = {p : E × ℝ | 0 ≤ p.2} := by ext p; simp [S]
  have hfS : ContDiffOn ℝ ∞ f S := by rwa [hSeq]
  have hS : IsClosed S := isClosed_univ.prod isClosed_Ici
  have hU : UniqueDiffOn ℝ S := UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Ici 0)
  obtain ⟨B, hB, hjet⟩ := MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
    f hf C hC hsupp
  have hflat : ∀ x ∈ frontier S, ∀ n : ℕ, iteratedFDerivWithin ℝ n (f - B) S x = 0 := by
    intro x hx n
    have hxS : x ∈ S := hS.frontier_subset hx
    have hx0 : x.2 = 0 := by
      simpa [S, frontier_univ_prod_eq, frontier_Ici] using hx
    obtain ⟨e, r⟩ := x
    dsimp at hx0
    subst r
    have hn : (n : ℕ∞ω) ≤ ∞ := (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le
    rw [iteratedFDerivWithin_sub_apply ((hfS (e, 0) hxS).of_le hn)
      (hB.contDiffWithinAt.of_le hn) hU hxS,
      iteratedFDerivWithin_eq_iteratedFDeriv (f := B) hU (hB.contDiffAt.of_le hn) hxS]
    have he := hjet n e
    simpa only [hSeq] using sub_eq_zero.mpr he.symm
  have hZ := contDiff_zero_extension_of_flat S hS hU (f - B) (hfS.sub hB.contDiffOn) hflat
  refine ⟨fun p => B p + S.indicator (f - B) p, hB.add hZ, ?_⟩
  intro p hp
  have hpS : p ∈ S := ⟨mem_univ _, hp⟩
  simp [hpS]

end SmoothJetExtension
namespace SmoothJetExtension
open Set Filter
open scoped ContDiff Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma exists_contDiff_weighted_strip_prefix
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ∞ f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → f p = 0)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (a : ℝ) (ha : a < 1) (hw0 : ∀ t, a ≤ t → w t = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ ∞ H ∧
      EqOn H (fun p => w p.2 • f p) {p : E × ℝ | 0 ≤ p.2} := by
  have hΨ : ContDiffOn ℝ ∞ (fun p : E × ℝ => w p.2 • f p) {p | 0 ≤ p.2} := by
    intro p hp
    by_cases hp1 : p.2 < 1
    · apply (hw.comp contDiff_snd).contDiffWithinAt.smul
      apply (hf p ⟨hp, hp1.le⟩).mono_of_mem_nhdsWithin
      have hnear : ∀ᶠ q : E × ℝ in 𝓝 p, q.2 < 1 :=
        (isOpen_lt continuous_snd continuous_const).mem_nhds hp1
      filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with q hq hq1
      exact ⟨hq, hq1.le⟩
    · have hpa : a < p.2 := lt_of_lt_of_le ha (not_lt.mp hp1)
      have hnear : ∀ᶠ q : E × ℝ in 𝓝 p, a < q.2 :=
        (isOpen_lt continuous_const continuous_snd).mem_nhds hpa
      have he : (fun p : E × ℝ => w p.2 • f p) =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [hnear] with q hq
        rw [hw0 q.2 hq.le, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
  exact exists_contDiff_extension_halfSpace _ hΨ C hC (fun p hp => by rw [hsupp p hp, smul_zero])

/-- A smooth function on a closed time strip, compactly supported in its spatial
variables, extends smoothly across both endpoints without changing its values. -/
lemma exists_contDiff_extension_strip
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ∞ f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → f p = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ ∞ H ∧
      EqOn H f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := by
  let θ : ℝ → ℝ := Real.smoothTransition
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  let w₀ : ℝ → ℝ := fun t => 1 - θ (2 * t - 1 / 2)
  let w₁ : ℝ → ℝ := fun t => θ (2 * (1 - t) - 1 / 2)
  have hw₀ : ContDiff ℝ ∞ w₀ := by dsimp [w₀]; fun_prop
  have hw₁ : ContDiff ℝ ∞ w₁ := by dsimp [w₁]; fun_prop
  have hw₀zero : ∀ t, (3 / 4 : ℝ) ≤ t → w₀ t = 0 := by
    intro t ht
    dsimp [w₀, θ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]
  have hw₁zero : ∀ t, (3 / 4 : ℝ) ≤ t → w₁ t = 0 := by
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  let rev : E × ℝ → E × ℝ := fun p => (p.1, 1 - p.2)
  have hrev : ContDiff ℝ ∞ rev := contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)
  have hfrev : ContDiffOn ℝ ∞ (f ∘ rev) {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := by
    apply hf.comp hrev.contDiffOn
    intro p hp
    dsimp [rev]
    constructor <;> linarith [hp.1, hp.2]
  obtain ⟨H₀, hH₀, hH₀eq⟩ := exists_contDiff_weighted_strip_prefix f hf C hC hsupp
    w₀ hw₀ (3 / 4) (by norm_num) hw₀zero
  obtain ⟨H₁, hH₁, hH₁eq⟩ := exists_contDiff_weighted_strip_prefix (f ∘ rev) hfrev C hC
    (fun p hp => hsupp (rev p) hp) w₁ hw₁ (3 / 4) (by norm_num) hw₁zero
  refine ⟨fun p => H₀ p + H₁ (rev p), hH₀.add (hH₁.comp hrev), ?_⟩
  intro p hp
  change H₀ p + H₁ (rev p) = f p
  rw [hH₀eq (x := p) hp.1, hH₁eq (x := rev p) (by dsimp [rev]; linarith [hp.2])]
  simp only [Function.comp_apply, rev, sub_sub_cancel, w₀, w₁]
  rw [← add_smul, sub_add_cancel, one_smul]

end SmoothJetExtension
open Set
open scoped ContDiff
theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ∞ f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → f p = 0) :
    ∃ H : E × ℝ → F, ContDiff ℝ ∞ H ∧
      EqOn H f {p : E × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := by
  exact SmoothJetExtension.exists_contDiff_extension_strip f hf C hC hsupp
