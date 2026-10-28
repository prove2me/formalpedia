-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.stonean_of_monotoneComplete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:07:35.471356+00:00
-- url     : https://prove2.me/submissions/71900d15-2955-487f-896c-051319ac8ad4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

namespace A3ST

open scoped Pointwise

theorem le_ap {K : Type u} [TopologicalSpace K] {f g : C(K, ℝ)} (h : f ≤ g) (x : K) :
    f x ≤ g x := h x

/-- The characteristic function of the closure of an open set is continuous. -/
theorem exists_char (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (hmono : HasPositiveMonotoneSuprema K)
    (U : Set K) (hU : IsOpen U) :
    ∃ g : C(K, ℝ), (∀ x ∈ closure U, g x = 1) ∧ (∀ x ∉ closure U, g x = 0) := by
  let S : Set C(K, ℝ) := {f | 0 ≤ f ∧ f ≤ 1 ∧ ∀ x ∉ U, f x = 0}
  have h0 : (0 : C(K, ℝ)) ∈ S := ⟨le_rfl, zero_le_one, fun _ _ => rfl⟩
  have hdir : DirectedOn (· ≤ ·) S := by
    intro f hf g hg
    refine ⟨f ⊔ g, ⟨le_sup_of_le_left hf.1, sup_le hf.2.1 hg.2.1, fun x hx => ?_⟩,
      le_sup_left, le_sup_right⟩
    simp [hf.2.2 x hx, hg.2.2 x hx]
  have hbd : ∃ R : ℝ, ∀ f ∈ S, ‖f‖ ≤ R := by
    refine ⟨1, fun f hf => ?_⟩
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro x
    have a := le_ap hf.1 x
    have b := le_ap hf.2.1 x
    simp only [ContinuousMap.zero_apply, ContinuousMap.one_apply] at a b
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  obtain ⟨g, hg⟩ := hmono S ⟨0, h0⟩ hdir (fun f hf => hf.1) hbd
  have hg1 : g ≤ 1 := hg.2 (fun f hf => hf.2.1)
  have hg0 : 0 ≤ g := hg.1 h0
  have hU1 : ∀ x ∈ U, g x = 1 := by
    intro x hx
    obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
      (isClosed_singleton (x := x)) (by simpa using hx)
    have hfS : f ∈ S := ⟨fun z => (hf z).1, fun z => (hf z).2,
      fun z hz => hf0 (show z ∈ Uᶜ from hz)⟩
    have := le_ap (hg.1 hfS) x
    have h2 := le_ap hg1 x
    have h3 : f x = 1 := hf1 rfl
    simp only [ContinuousMap.one_apply] at h2
    linarith
  refine ⟨g, ?_, ?_⟩
  · have : closure U ⊆ {x | g x = 1} :=
      closure_minimal hU1 (isClosed_eq g.continuous continuous_const)
    exact fun x hx => this hx
  · intro y hy
    obtain ⟨h, hh0, hh1, hh⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := y)) isClosed_closure (by simpa using hy)
    have hub : h ∈ upperBounds S := by
      intro f hf z
      show f z ≤ h z
      by_cases hz : z ∈ U
      · have := le_ap hf.2.1 z
        rw [hh1 (subset_closure hz)]
        simpa using this
      · rw [hf.2.2 z hz]; exact (hh z).1
    have := le_ap (hg.2 hub) y
    have h3 : h y = 0 := hh0 rfl
    have h4 := le_ap hg0 y
    simp only [ContinuousMap.zero_apply] at h4
    linarith

theorem clopen (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (hmono : HasPositiveMonotoneSuprema K)
    (U : Set K) (hU : IsOpen U) : IsOpen (closure U) := by
  obtain ⟨g, h1, h0⟩ := exists_char K hmono U hU
  have : closure U = g ⁻¹' Ioi (1 / 2) := by
    ext x
    by_cases hx : x ∈ closure U
    · simp [hx, h1 x hx]; norm_num
    · simp [hx, h0 x hx]
  rw [this]
  exact isOpen_Ioi.preimage g.continuous

theorem main (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (hmono : HasPositiveMonotoneSuprema K) :
    (∀ U : Set K, IsOpen U → IsOpen (closure U)) ∧
      (Submodule.span ℂ {f : C(K, ℂ) | IsStarProjection f}).topologicalClosure = ⊤ := by
  refine ⟨clopen K hmono, ?_⟩
  set P : Set C(K, ℂ) := {f : C(K, ℂ) | IsStarProjection f} with hP
  set M := Submodule.span ℂ P with hM
  have hPmul : P * P ⊆ P := by
    rintro _ ⟨p, hp, q, hq, rfl⟩
    exact hp.mul hq (Commute.all p q)
  have hmul : ∀ x y, x ∈ M → y ∈ M → x * y ∈ M := by
    intro x y hx hy
    have : x * y ∈ M * M := Submodule.mul_mem_mul hx hy
    rw [hM, Submodule.span_mul_span] at this
    exact Submodule.span_mono hPmul this
  have hone : (1 : C(K, ℂ)) ∈ M := Submodule.subset_span (IsStarProjection.one _)
  have hstar : ∀ x ∈ M, star x ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [hx.isSelfAdjoint.star_eq]; exact Submodule.subset_span hx
    | zero => simp
    | add x y _ _ h1 h2 => rw [star_add]; exact M.add_mem h1 h2
    | smul a x _ h => rw [star_smul]; exact M.smul_mem _ h
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { (M.toSubalgebra hone hmul) with star_mem' := fun {x} hx => hstar x hx }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨V, W, hV, hW, hxV, hyW, hVW⟩ := t2_separation hxy
    have hyc : y ∉ closure V := by
      intro hc
      have := (mem_closure_iff.mp hc) W hW hyW
      obtain ⟨z, hzW, hzV⟩ := this
      exact Set.disjoint_left.mp hVW hzV hzW
    obtain ⟨g, h1, h0⟩ := exists_char K hmono V hV
    let gc : C(K, ℂ) := ⟨fun z => (g z : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
    have hgc : IsStarProjection gc := by
      constructor
      · ext z
        simp only [ContinuousMap.mul_apply, gc, ContinuousMap.coe_mk]
        by_cases hz : z ∈ closure V
        · simp [h1 z hz]
        · simp [h0 z hz]
      · ext z
        simp [gc]
    refine ⟨gc, ⟨gc, Submodule.subset_span hgc, rfl⟩, ?_⟩
    simp [gc, h1 x (subset_closure hxV), h0 y hyc]
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ A.topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hf
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact hf

end A3ST

end QAlgorithms.Papers.Independent.Renew46.P02

end

universe u

theorem solution (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K]
    (hmono : QAlgorithms.Papers.Independent.Renew46.P02.HasPositiveMonotoneSuprema K) :
    (∀ U : Set K, IsOpen U → IsOpen (closure U)) ∧
      (Submodule.span ℂ {f : C(K, ℂ) | IsStarProjection f}).topologicalClosure = ⊤ :=
  QAlgorithms.Papers.Independent.Renew46.P02.A3ST.main K hmono
