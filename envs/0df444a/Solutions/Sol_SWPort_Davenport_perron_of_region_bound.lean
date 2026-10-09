-- Prove2me | solution 1 for SWPort.Davenport.perron_of_region_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:44.290233+00:00
-- url     : https://prove2.me/submissions/959c9a32-b729-4d67-b579-0793a944a079

import Mathlib
import Definitions.Def_SWPort_001

section
-- module Solutions.Artin.SW.Thm.HolomorphicOn_vanishesOnRectangle
namespace SWPort
/-! Ported from prove2.me: `HolomorphicOn.vanishesOnRectangle` (9545a167-c26e-42b4-a31e-6b0da9ea9f41, statement by Community (Bot)); proof = accepted direct submission 54348a9e-624c-4bbc-9145-0e2421394525 by Community (Bot). -/












open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.SWPort.HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.IsBigO_to_BddAbove
namespace SWPort
/-! Ported from prove2.me: `IsBigO_to_BddAbove` (9679d93e-eb72-4a91-9e81-ff4618976134, statement by Community (Bot)); proof = accepted direct submission 9ffe6794-56f8-4e92-8a26-a32e3b220800 by Community (Bot). -/












open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.SWPort.IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, mem_diff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.existsDifferentiableOn_of_bddAbove
namespace SWPort
/-! Ported from prove2.me: `existsDifferentiableOn_of_bddAbove` (dc84894c-d500-4dce-9c12-f004772b9cf6, statement by Community (Bot)); proof = accepted direct submission 5099e0df-cbca-4fc9-9991-1a2549e17f05 by Community (Bot). -/












open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.SWPort.existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_left_im
namespace SWPort
/-! Ported from prove2.me: `mapsTo_rectangleBorder_left_im` (e7072fdd-3190-4349-9824-672ed7f6cf10, statement by Community (Bot)); proof = accepted direct submission d3f774b3-f08b-4c42-a2b1-b1dba24da366 by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_left_re
namespace SWPort
/-! Ported from prove2.me: `mapsTo_rectangleBorder_left_re` (58a6d1e7-fb5d-479c-b33d-a2cad2193a8d, statement by Community (Bot)); proof = accepted direct submission 01260408-219a-49a4-83e3-215fa93c8dee by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_right_im
namespace SWPort
/-! Ported from prove2.me: `mapsTo_rectangleBorder_right_im` (db6b635b-9391-44f3-8b91-1e5a6b9f6e28, statement by Community (Bot)); proof = accepted direct submission 723fc351-35c3-49ac-809f-eda7e8d55d83 by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_right_re
namespace SWPort
/-! Ported from prove2.me: `mapsTo_rectangleBorder_right_re` (9bf0ecd2-4d6c-4f13-92c8-b80e5002d20a, statement by Community (Bot)); proof = accepted direct submission 2e11baed-c579-4baf-b664-a206e5e44616 by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.rectangle_mem_nhds_iff
namespace SWPort
/-! Ported from prove2.me: `rectangle_mem_nhds_iff` (6acc033d-4619-41c3-9897-aeffeb433822, statement by Community (Bot)); proof = accepted direct submission 59d17d34-2c35-4e41-82da-0f2b7d4a2a3c by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.not_mem_rectangleBorder_of_rectangle_mem_nhds
namespace SWPort
/-! Ported from prove2.me: `not_mem_rectangleBorder_of_rectangle_mem_nhds` (d2ce0450-2d8e-4253-9421-c254e63992cd, statement by Community (Bot)); proof = accepted sketch submission cfcdf00e-dd69-4098-a362-d468f2bb6b9b by Community (Bot). -/






open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

private theorem _root_.Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

private theorem _root_.Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

private theorem _root_.Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

private theorem rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

theorem _root_.SWPort.not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.rectangleBorder_subset_rectangle
namespace SWPort
/-! Ported from prove2.me: `rectangleBorder_subset_rectangle` (27c9e576-b409-45cb-b295-116f3f8a1e5a, statement by Community (Bot)); proof = accepted direct submission b468ed91-03cd-4774-a2ff-4c6133145b93 by Community (Bot). -/





open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

theorem _root_.SWPort.rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.ResidueTheoremOnRectangleWithSimplePole_prime
namespace SWPort
/-! Ported from prove2.me: `ResidueTheoremOnRectangleWithSimplePole_prime` (de1ab0a9-354d-4b8c-b836-bb3f087bdb7a, statement by Community (Bot)); proof = accepted sketch submission 3b52f320-4c89-40f8-b5d9-72a8cda7ab1d by Community (Bot). -/






















open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

private theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

private theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

private theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem _root_.ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
private theorem _root_.ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
private theorem _root_.ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_diff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

private theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

private theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

private theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

private theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

private theorem _root_.Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

private theorem sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

private theorem continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

private theorem integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1 <;> try with_reducible_and_instances rfl
    first | ring | (norm_num; ring) | field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

private theorem integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option backward.isDefEq.respectTransparency false in
private theorem integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

private theorem integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

private theorem ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

private theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

private theorem ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_diff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    HolomorphicOn.rectangleBorderIntegrable gHolo
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [HolomorphicOn.vanishesOnRectangle gHolo (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

private theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [mem_diff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply diff_subset_diff_right
      simpa
  · exact V_prop.mono
      (image_mono <| diff_subset_diff_left <| subset_trans inter_subset_right W_subset)

theorem _root_.SWPort.ResidueTheoremOnRectangleWithSimplePole_prime {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_perron_of_region_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.perron_of_region_bound` (e1f52231-1959-47c4-9cfb-ac1eb539c322, statement by alya); proof = accepted sketch submission ea5571ed-35e5-4b15-af08-e7266dcc30ca by alya. -/




























open Finset DirichletCharacter Vino
open Complex Real Set MeasureTheory intervalIntegral Filter Topology

namespace Davenport
namespace TP

/-! ### Piece `Sums` -/

/-! ### Helpers for (G1)/(G2) -/

/-- Termwise bound `Λ n / n^σ ≤ (1/δ) n^(-1-δ)` with `δ = (σ-1)/2`. -/
private theorem g_term_le {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ
      ≤ (1 / ((σ - 1) / 2)) * (n : ℝ) ^ (-1 - (σ - 1) / 2) := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, ArithmeticFunction.map_zero, zero_div]
    exact mul_nonneg (by positivity) (Real.zero_rpow_nonneg _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have h2 : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hn'.le hδpos
  have h3 : (n : ℝ) ^ (-1 - δ) = (n : ℝ) ^ δ / (n : ℝ) ^ σ := by
    rw [← Real.rpow_sub hn']
    congr 1
    rw [hδ]; ring
  rw [h3]
  have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn' σ
  rw [div_le_iff₀ hpos]
  calc (ArithmeticFunction.vonMangoldt n : ℝ) ≤ (n : ℝ) ^ δ / δ := h1.trans h2
    _ = 1 / δ * ((n : ℝ) ^ δ / (n : ℝ) ^ σ) * (n : ℝ) ^ σ := by
        field_simp

/-- Nonnegativity of the terms. -/
private theorem g_term_nonneg {σ : ℝ} (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
  apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
  exact Real.rpow_nonneg (Nat.cast_nonneg n) σ

/-- (G1) Summability of `Λ n / n^σ` for `σ > 1`. -/
private theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  have hs : Summable (fun n : ℕ => (1 / ((σ - 1) / 2)) * (n : ℝ) ^ (-1 - (σ - 1) / 2)) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  exact Summable.of_nonneg_of_le (fun n => g_term_nonneg n) (fun n => g_term_le hσ n) hs

/-! ### (G2) -/

/-- Partial sums of `n^(-1-δ)` are bounded by `1 + 1/δ`. -/
private theorem g_sum_rpow_le {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (i : ℝ) ^ (-1 - δ) ≤ 1 + 1 / δ := by
  have hδ' : 0 ≤ 1 / δ := by positivity
  have hexp : (-1 - δ) ≠ 0 := by linarith
  rcases M with _ | M
  · simp; positivity
  rcases M with _ | a
  · simp [Real.zero_rpow hexp]; positivity
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.cast_zero, Nat.cast_one, Real.one_rpow, zero_add, Real.zero_rpow hexp, add_zero]
  -- the tail `∑_{i < a} (i+2)^(-1-δ)` is bounded by the integral `∫_1^{1+a} x^(-1-δ)`
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1 - δ)) (Icc 1 (1 + (a : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint := hanti.sum_le_integral
  have hI : ∫ x in (1 : ℝ)..(1 + (a : ℝ)), x ^ (-1 - δ)
      = ((1 + (a : ℝ)) ^ (-1 - δ + 1) - (1 : ℝ) ^ (-1 - δ + 1)) / (-1 - δ + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hle : ((1 + (a : ℝ)) ^ (-1 - δ + 1) - (1 : ℝ) ^ (-1 - δ + 1)) / (-1 - δ + 1) ≤ 1 / δ := by
    rw [Real.one_rpow, show (-1 - δ + 1) = -δ by ring]
    have h0 : 0 ≤ (1 + (a : ℝ)) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    rw [div_le_iff_of_neg (by linarith)]
    have : 1 / δ * (-δ) = -1 := by field_simp
    rw [this]
    linarith
  have hsum : ∑ i ∈ Finset.range a, ((i : ℝ) + 1 + 1) ^ (-1 - δ)
      = ∑ i ∈ Finset.range a, (fun x : ℝ => x ^ (-1 - δ)) (1 + ((i + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only
    congr 1
    push_cast
    ring
  have key : ∑ i ∈ Finset.range a, ((i : ℝ) + 1 + 1) ^ (-1 - δ) ≤ 1 / δ := by
    rw [hsum]
    exact hint.trans (hI ▸ hle)
  push_cast
  linarith

/-- (G2) Explicit bound `∑ Λ n / n^σ ≤ 8 / (σ - 1)^2` for `1 < σ ≤ 3`. -/
private theorem tsum_vonMangoldt_div_rpow_le {σ : ℝ} (hσ : 1 < σ) (hσ3 : σ ≤ 3) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ ≤ 8 / (σ - 1) ^ 2 := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  apply Real.tsum_le_of_sum_range_le (fun n => g_term_nonneg n)
  intro M
  calc ∑ i ∈ Finset.range M, (ArithmeticFunction.vonMangoldt i : ℝ) / (i : ℝ) ^ σ
      ≤ ∑ i ∈ Finset.range M, (1 / δ) * (i : ℝ) ^ (-1 - δ) :=
        Finset.sum_le_sum (fun i _ => g_term_le hσ i)
    _ = (1 / δ) * ∑ i ∈ Finset.range M, (i : ℝ) ^ (-1 - δ) := by rw [Finset.mul_sum]
    _ ≤ (1 / δ) * (1 + 1 / δ) := by
        apply mul_le_mul_of_nonneg_left (g_sum_rpow_le hδpos M)
        positivity
    _ ≤ (1 / δ) * (2 / δ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show (2 : ℝ) / δ = 1 / δ + 1 / δ by ring]
        have : 1 ≤ 1 / δ := by
          rw [le_div_iff₀ hδpos]; linarith
        linarith
    _ = 8 / (σ - 1) ^ 2 := by
        rw [hδ]; field_simp; ring

/-! ### (G3) -/

/-- (G3) Elementary: for `x > 0`, `n ≥ 1`, `n ≠ x`: `1/|log (x/n)| ≤ 1/log 2 + 2x/|x - n|`. -/
private theorem one_div_abs_log_le {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hxn : (n : ℝ) ≠ x) :
    1 / |Real.log (x / n)| ≤ 1 / Real.log 2 + 2 * x / |x - n| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℝ := x / n with hy
  have hy0 : 0 < y := div_pos hx hn'
  have hy1 : y ≠ 1 := by
    rw [hy]; intro h
    rw [div_eq_one_iff_eq hn'.ne'] at h
    exact hxn h.symm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy0 hy1
  have habs : 0 < |Real.log y| := abs_pos.mpr hlogy
  have hxn' : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hxn))
  have hA : 0 ≤ 2 * x / |x - n| := by positivity
  have hB : 0 ≤ 1 / Real.log 2 := by positivity
  -- helper: from `a ≤ |log y|` with `a > 0` get `1/|log y| ≤ 1/a`
  by_cases h2 : 2 ≤ y
  · have : Real.log 2 ≤ |Real.log y| := by
      rw [abs_of_pos (Real.log_pos (by linarith))]
      exact Real.log_le_log (by norm_num) h2
    calc 1 / |Real.log y| ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 this
      _ ≤ _ := by linarith
  by_cases h3 : y ≤ 1 / 2
  · have : Real.log 2 ≤ |Real.log y| := by
      have hlt : Real.log y < 0 := Real.log_neg hy0 (by linarith)
      rw [abs_of_neg hlt]
      have := Real.log_le_log hy0 h3
      rw [one_div, Real.log_inv] at this
      linarith
    calc 1 / |Real.log y| ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 this
      _ ≤ _ := by linarith
  push Not at h2 h3
  -- middle case: `1/2 < y < 2`
  have hkey : |x - n| / (2 * x) ≤ |Real.log y| := by
    have hn2 : (n : ℝ) < 2 * x := by
      rw [hy, lt_div_iff₀ hn'] at h3; linarith
    have hx2 : x < 2 * n := by
      rw [hy, div_lt_iff₀ hn'] at h2; linarith
    rcases lt_or_gt_of_ne hy1 with hlt | hgt
    · -- `y < 1`, i.e. `x < n`
      have hxn2 : x < n := by rw [hy, div_lt_one hn'] at hlt; exact hlt
      have hl : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
      have hneg : Real.log y < 0 := Real.log_neg hy0 hlt
      rw [abs_of_neg hneg, abs_of_neg (by linarith)]
      have : 1 - y = (n - x) / n := by rw [hy]; field_simp
      rw [div_le_iff₀ (by positivity)]
      calc -(x - n) = (n - x) := by ring
        _ ≤ (1 - y) * (2 * x) := by
            rw [this, div_mul_eq_mul_div, le_div_iff₀ hn']
            nlinarith
        _ ≤ -Real.log y * (2 * x) := by nlinarith
    · -- `y > 1`, i.e. `x > n`
      have hxn2 : (n : ℝ) < x := by rw [hy, one_lt_div hn'] at hgt; exact hgt
      have hl : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy0
      have hpos : 0 < Real.log y := Real.log_pos hgt
      rw [abs_of_pos hpos, abs_of_pos (by linarith)]
      have : 1 - y⁻¹ = (x - n) / x := by rw [hy, inv_div]; field_simp
      rw [div_le_iff₀ (by positivity)]
      calc x - n ≤ (1 - y⁻¹) * (2 * x) := by
            rw [this, div_mul_eq_mul_div, le_div_iff₀ hx]
            nlinarith
        _ ≤ Real.log y * (2 * x) := by nlinarith
  calc 1 / |Real.log y| ≤ 1 / (|x - n| / (2 * x)) :=
        one_div_le_one_div_of_le (by positivity) hkey
    _ = 2 * x / |x - n| := by rw [one_div_div]
    _ ≤ _ := by linarith

/-! ### (G4) -/

/-- Distance of the half-integer `x = N - 1/2` to any natural number is at least `1/2`. -/
private theorem g_abs_sub_ge {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) (n : ℕ) :
    1 / 2 ≤ |x - n| := by
  rcases lt_or_ge n N with h | h
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have : (N : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith

private theorem g_ne_of_half {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) (n : ℕ) : (n : ℝ) ≠ x := by
  intro h
  have := g_abs_sub_ge hx n
  rw [h, sub_self, abs_zero] at this
  linarith

/-- (G4) Summability of the Perron error terms, `x = N - 1/2`. -/
private theorem summable_perron_error {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
      |Real.log (x / n)|) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS := summable_vonMangoldt_div_rpow hσ₀
  have hC : 0 ≤ x ^ σ₀ * (1 / Real.log 2 + 4 * x) := by positivity
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hS.mul_left (x ^ σ₀ * (1 / Real.log 2 + 4 * x)))
  · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity) _)) (abs_nonneg _)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hn1 : 1 ≤ n := hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hG3 := one_div_abs_log_le hx0 hn1 (g_ne_of_half hx n)
      have habs := g_abs_sub_ge hx n
      have h4 : 2 * x / |x - n| ≤ 4 * x := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      have hterm : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
          = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
            ring
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / Real.log 2 + 4 * x) :=
            mul_le_mul_of_nonneg_left (hG3.trans (by linarith)) hterm
        _ = x ^ σ₀ * (1 / Real.log 2 + 4 * x) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀) := by
            rw [Real.div_rpow hx0.le hn'.le]; ring

/-! ### (C') -/

private theorem g_log_two_ge : 1 / 2 ≤ Real.log 2 := by
  have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at this
  linarith

private theorem g_log_two_le : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- The real harmonic number as a `range` sum. -/
private theorem g_harmonic_eq (N : ℕ) : (harmonic N : ℝ) = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
  simp [harmonic, one_div]

/-- Harmonic-type bound: `∑_{n < 2N} 1/|x - n| ≤ 4 (1 + log N)` for `x = N - 1/2`. -/
private theorem g_sum_inv_abs_le {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∑ n ∈ Finset.range (2 * N), 1 / |x - n| ≤ 4 * (1 + Real.log N) := by
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have h1 : ∑ n ∈ Finset.range N, 1 / |x - n| ≤ 2 * (harmonic N : ℝ) := by
    calc ∑ n ∈ Finset.range N, 1 / |x - n|
        ≤ ∑ n ∈ Finset.range N, 2 * (1 / (((N - 1 - n : ℕ) : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_range] at hn
          have hcast : ((N - 1 - n : ℕ) : ℝ) + 1 = N - n := by
            rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
          rw [hcast]
          have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
          rw [abs_of_pos (by linarith), div_le_iff₀ (by linarith), mul_one_div,
            div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          linarith
      _ = ∑ j ∈ Finset.range N, 2 * (1 / ((j : ℝ) + 1)) :=
          Finset.sum_range_reflect (fun j : ℕ => 2 * (1 / ((j : ℝ) + 1))) N
      _ = 2 * (harmonic N : ℝ) := by rw [g_harmonic_eq, Finset.mul_sum]
  have h2 : ∑ n ∈ Finset.range N, 1 / |x - ((N + n : ℕ) : ℝ)| ≤ 2 * (harmonic N : ℝ) := by
    rw [g_harmonic_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
    have habs : |x - ((N + n : ℕ) : ℝ)| = n + 1 / 2 := by
      push_cast
      rw [abs_of_neg (by linarith)]
      linarith
    rw [habs, div_le_iff₀ hpos, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  rw [two_mul, Finset.sum_range_add]
  linarith

private theorem g_hB_nonneg {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx0 : 0 < x) (n : ℕ) : 0 ≤ g_hB N x n := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  unfold g_hB
  split_ifs
  · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  · exact le_rfl

private theorem g_hB_supp {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∀ n ∉ Finset.range (2 * N), g_hB N x n = 0 := by
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have : (2 * N : ℝ) ≤ n := by exact_mod_cast hn
  unfold g_hB
  rw [if_neg]
  rintro ⟨_, h2⟩
  linarith

private theorem g_hB_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx0 : 0 < x) (n : ℕ) :
    g_hB N x n ≤ 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  unfold g_hB
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)

/-- The finite class-B sum. -/
private theorem g_sum_hB_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∑ n ∈ Finset.range (2 * N), g_hB N x n ≤ 96 * N * (1 + Real.log N) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL : 1 ≤ 1 + Real.log N := by linarith
  have hsig := g_sum_inv_abs_le hx
  calc ∑ n ∈ Finset.range (2 * N), g_hB N x n
      ≤ ∑ n ∈ Finset.range (2 * N), 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) :=
        Finset.sum_le_sum (fun n _ => g_hB_le hN hx0 n)
    _ = 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
          + 8 * (1 + Real.log N) * (2 * x) * ∑ n ∈ Finset.range (2 * N), 1 / |x - n| := by
        rw [Finset.mul_sum]
        have : 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
            = ∑ n ∈ Finset.range (2 * N), 8 * (1 + Real.log N) * 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        rw [this, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
          + 8 * (1 + Real.log N) * (2 * x) * (4 * (1 + Real.log N)) := by
        have hc : 0 ≤ 8 * (1 + Real.log N) * (2 * x) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
        have := mul_le_mul_of_nonneg_left hsig hc
        linarith
    _ = 32 * N * (1 + Real.log N) + 64 * x * (1 + Real.log N) ^ 2 := by ring
    _ ≤ 32 * N * (1 + Real.log N) ^ 2 + 64 * N * (1 + Real.log N) ^ 2 := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by linarith)
          nlinarith
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
    _ = 96 * N * (1 + Real.log N) ^ 2 := by ring

/-- Pointwise bound `f n ≤ g n + h n` for the Perron error terms. -/
private theorem g_pointwise {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀) + g_hB N x n := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 := g_hB_nonneg hN hx0 n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, ArithmeticFunction.map_zero, zero_mul, zero_div, mul_zero, zero_add]
    exact hh0
  have hn1 : 1 ≤ n := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < x / n := div_pos hx0 hn'
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hyσ : 0 ≤ (x / n) ^ σ₀ := Real.rpow_nonneg hy0.le _
  have hterm : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ := mul_nonneg hΛ0 hyσ
  have hgn : 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
      = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) := by
    rw [Real.div_rpow hx0.le hn'.le]; ring
  rw [hgn]
  have hne : (n : ℝ) ≠ x := g_ne_of_half hx n
  by_cases hB : x / 2 < n ∧ (n : ℝ) < 2 * x
  · -- class B
    have hhn : g_hB N x n = 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) := by
      unfold g_hB; rw [if_pos hB]
    have hG3 := one_div_abs_log_le hx0 hn1 hne
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1 + Real.log N := by
      calc (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
            ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (2 * N) := Real.log_le_log hn' (by rw [hx] at hB; linarith [hB.2])
        _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + Real.log N := by linarith [g_log_two_le]
    have hy2 : (x / n) ^ σ₀ ≤ 8 := by
      calc (x / n) ^ σ₀ ≤ (2 : ℝ) ^ σ₀ :=
            Real.rpow_le_rpow hy0.le (by rw [div_le_iff₀ hn']; linarith [hB.1]) (by linarith)
        _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ₀3
        _ = 8 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hl2 : 1 / Real.log 2 ≤ 2 := by
      rw [div_le_iff₀ hlog2]; linarith [g_log_two_ge]
    have hA0 : 0 ≤ 2 * x / |x - n| := by positivity
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
          ring
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ *
            (1 / Real.log 2 + 2 * x / |x - n|) := mul_le_mul_of_nonneg_left hG3 hterm
      _ ≤ (1 + Real.log N) * 8 * (2 + 2 * x / |x - n|) := by
          apply mul_le_mul (mul_le_mul hΛ hy2 hyσ (by linarith)) (by linarith)
            (add_nonneg (by positivity) hA0) (by positivity)
      _ = g_hB N x n := by rw [hhn]; ring
      _ ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) + g_hB N x n := by
          linarith
  · -- class A: `|log (x/n)| ≥ log 2 ≥ 1/2`
    have hhn : g_hB N x n = 0 := by unfold g_hB; rw [if_neg hB]
    have hlog : 1 / 2 ≤ |Real.log (x / n)| := by
      by_cases hn2 : x / 2 < n
      · have h2 : 2 * x ≤ n := by
          by_contra hcon
          exact hB ⟨hn2, by linarith⟩
        have : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hn']; linarith
        have hneg : Real.log (x / n) < 0 := Real.log_neg hy0 (by linarith)
        rw [abs_of_neg hneg]
        have := Real.log_le_log hy0 this
        rw [one_div, Real.log_inv] at this
        linarith [g_log_two_ge]
      · push Not at hn2
        have : 2 ≤ x / n := by rw [le_div_iff₀ hn']; linarith
        rw [abs_of_pos (Real.log_pos (by linarith))]
        calc 1 / 2 ≤ Real.log 2 := g_log_two_ge
          _ ≤ Real.log (x / n) := Real.log_le_log (by norm_num) this
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
          ring
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * 2 := by
          apply mul_le_mul_of_nonneg_left _ hterm
          calc 1 / |Real.log (x / n)| ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hlog
            _ = 2 := by norm_num
      _ = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) + g_hB N x n := by
          rw [hhn]; ring

/-- (C') Bound for the Perron error sum, `x = N - 1/2`, `1 < σ₀ ≤ 3`. -/
private theorem perron_error_sum_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ 10 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
        + 100 * N * (1 + Real.log N) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hS0 : 0 ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ :=
    tsum_nonneg (fun n => g_term_nonneg n)
  have hSsum := summable_vonMangoldt_div_rpow hσ₀
  have hf := summable_perron_error hN hx hσ₀
  have hg : Summable (fun n : ℕ =>
      2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)) :=
    hSsum.mul_left _
  have hh : Summable (fun n : ℕ => g_hB N x n) := summable_of_ne_finset_zero (g_hB_supp hx)
  have hxσ : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx0.le _
  have hNL : 0 ≤ (N : ℝ) * (1 + Real.log N) ^ 2 := by positivity
  calc ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ ∑' n : ℕ, (2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + g_hB N x n) :=
        Summable.tsum_le_tsum (fun n => g_pointwise hN hx hσ₀ hσ₀3 n) hf (hg.add hh)
    _ = ∑' n : ℕ, 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + ∑' n : ℕ, g_hB N x n := hg.tsum_add hh
    _ = 2 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + ∑ n ∈ Finset.range (2 * N), g_hB N x n := by
        rw [tsum_mul_left, tsum_eq_sum (g_hB_supp hx)]
    _ ≤ 2 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + 96 * N * (1 + Real.log N) ^ 2 := by
        linarith [g_sum_hB_le hN hx]
    _ ≤ _ := by nlinarith


/-! ### Piece `Kernel` -/

/-! ### Basic facts about `s ↦ y^s / s` -/

/-- Differentiability of `s ↦ y^s / s` away from `0`. -/
private theorem k_differentiableAt {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s / s) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  exact h1.div differentiableAt_id hs

/-- Pointwise bound on a horizontal line `Im s = t ≠ 0`. -/
private theorem k_norm_le {y : ℝ} (hy : 0 < y) {σ t : ℝ} (ht : t ≠ 0) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖ ≤ y ^ σ / |t| := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hpos : 0 < ‖(σ : ℂ) + t * I‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht this
  have hle : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
    rwa [him] at this
  have hy' : 0 ≤ y ^ σ := (Real.rpow_pos_of_pos hy σ).le
  exact div_le_div_of_nonneg_left hy' (abs_pos.mpr ht) hle

/-- Pointwise bound on a vertical line `Re s = σ ≠ 0`. -/
private theorem k_norm_le' {y : ℝ} (hy : 0 < y) {σ t : ℝ} (hσ : σ ≠ 0) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖ ≤ y ^ σ / |σ| := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hpos : 0 < ‖(σ : ℂ) + t * I‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ this
  have hle : |σ| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
    rwa [hre] at this
  have hy' : 0 ≤ y ^ σ := (Real.rpow_pos_of_pos hy σ).le
  exact div_le_div_of_nonneg_left hy' (abs_pos.mpr hσ) hle

/-- Continuity of `σ ↦ y^σ`. -/
private theorem k_continuous_rpow {y : ℝ} (hy : 0 < y) : Continuous (fun σ : ℝ => y ^ σ) :=
  continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')

/-- The integral of `y^σ`. -/
private theorem k_integral_rpow {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (σ₁ σ₂ : ℝ) :
    ∫ σ in σ₁..σ₂, y ^ σ = (y ^ σ₂ - y ^ σ₁) / Real.log y := by
  have hlog : Real.log y ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact hy.ne' h
    · exact hy1 h
    · linarith
  have hderiv : ∀ σ ∈ uIcc σ₁ σ₂,
      HasDerivAt (fun σ : ℝ => y ^ σ / Real.log y) (y ^ σ) σ := by
    intro σ _
    have := ((Real.hasStrictDerivAt_const_rpow hy σ).hasDerivAt).div_const (Real.log y)
    rwa [mul_div_cancel_right₀ _ hlog] at this
  rw [integral_eq_sub_of_hasDerivAt hderiv ((k_continuous_rpow hy).intervalIntegrable _ _)]
  ring

/-- Bound for the horizontal integral of `y^s/s` on `Im s = t ≠ 0`. -/
private theorem k_horizontal_le {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : t ≠ 0) {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    ‖∫ σ in σ₁..σ₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ (1 / |t|) * ∫ σ in σ₁..σ₂, y ^ σ := by
  have hb : ‖∫ σ in σ₁..σ₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ ∫ σ in σ₁..σ₂, y ^ σ / |t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le h (Eventually.of_forall ?_) ?_
    · intro σ _
      exact k_norm_le hy ht
    · exact ((k_continuous_rpow hy).div_const _).intervalIntegrable _ _
  refine hb.trans (le_of_eq ?_)
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext σ
  ring

/-- Bound for the vertical integral of `y^s/s` on `Re s = σ ≠ 0`. -/
private theorem k_vertical_le {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : σ ≠ 0) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    ‖∫ t in t₁..t₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ σ / |σ| * (t₂ - t₁) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t₁) (b := t₂) (C := y ^ σ / |σ|)
    (f := fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
    (fun t _ => k_norm_le' hy hσ)
  rw [abs_of_nonneg (sub_nonneg.mpr h)] at this
  exact this

/-- Cauchy's theorem on a rectangle with real coordinates. -/
private theorem k_cauchy {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (H : DifferentiableOn ℂ f (Set.uIcc x₁ x₂ ×ℂ Set.uIcc y₁ y₂)) :
    (∫ x : ℝ in x₁..x₂, f (x + y₁ * I)) - (∫ x : ℝ in x₁..x₂, f (x + y₂ * I)) +
      I • (∫ y : ℝ in y₁..y₂, f (x₂ + y * I)) -
      I • (∫ y : ℝ in y₁..y₂, f (x₁ + y * I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ H

/-- The horizontal edge integrals of `y^s/s` are bounded by `y^a / (|t| * (-log y))`
(`y < 1`, `U ≥ 0`). -/
private theorem k_horizontal_lt_one {y a U : ℝ} (hy0 : 0 < y) (hy : y < 1) {t : ℝ} (ht : t ≠ 0)
    (hU : 0 ≤ U) :
    ‖∫ σ in a..a + U, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ a / (-Real.log y) * (1 / |t|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy
  refine (k_horizontal_le hy0 ht (by linarith)).trans ?_
  rw [k_integral_rpow hy0 hy.ne a (a + U)]
  have h1 : 0 ≤ y ^ (a + U) := (Real.rpow_pos_of_pos hy0 _).le
  have h2 : (y ^ (a + U) - y ^ a) / Real.log y ≤ y ^ a / (-Real.log y) := by
    rw [show (y ^ (a + U) - y ^ a) / Real.log y = (y ^ a - y ^ (a + U)) / (-Real.log y) by
      rw [div_neg, ← neg_div, neg_sub]]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc (1 / |t|) * ((y ^ (a + U) - y ^ a) / Real.log y)
      ≤ (1 / |t|) * (y ^ a / (-Real.log y)) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = y ^ a / (-Real.log y) * (1 / |t|) := by ring

/-- The horizontal edge integrals of `y^s/s` are bounded by `y^a / (|t| * log y)`
(`y > 1`, `U ≥ 0`). -/
private theorem k_horizontal_gt_one {y a U : ℝ} (hy : 1 < y) {t : ℝ} (ht : t ≠ 0)
    (hU : 0 ≤ U) :
    ‖∫ σ in a - U..a, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ a / Real.log y * (1 / |t|) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  refine (k_horizontal_le hy0 ht (by linarith)).trans ?_
  rw [k_integral_rpow hy0 hy.ne' (a - U) a]
  have h1 : 0 ≤ y ^ (a - U) := (Real.rpow_pos_of_pos hy0 _).le
  have h2 : (y ^ a - y ^ (a - U)) / Real.log y ≤ y ^ a / Real.log y := by
    apply div_le_div_of_nonneg_right _ hlog.le
    linarith
  calc (1 / |t|) * ((y ^ a - y ^ (a - U)) / Real.log y)
      ≤ (1 / |t|) * (y ^ a / Real.log y) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = y ^ a / Real.log y * (1 / |t|) := by ring

/-- Norm of the constant `1 / (2π)`. -/
private theorem k_norm_two_pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
  have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- (K2), one rectangle: the bound with the right-edge error term. -/
private theorem k_lt_one_step {y a t₁ t₂ U : ℝ} (hy0 : 0 < y) (hy : y < 1) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) (hU : 0 < U) :
    ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖
      ≤ y ^ a / (-Real.log y) * (1 / (-t₁) + 1 / t₂) + y ^ (a + U) / (a + U) * (t₂ - t₁) := by
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  have hdiff : DifferentiableOn ℂ f (Set.uIcc a (a + U) ×ℂ Set.uIcc t₁ t₂) := by
    intro s hs
    apply (k_differentiableAt hy0 _).differentiableWithinAt
    intro h0
    rw [Complex.mem_reProdIm, h0, Set.uIcc_of_le (by linarith)] at hs
    have := hs.1
    simp at this
    linarith
  have hc := k_cauchy hdiff
  rw [sub_eq_zero] at hc
  have hnorm : ‖∫ t in t₁..t₂, f (a + t * I)‖ = ‖I • ∫ t in t₁..t₂, f (a + t * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have hB := k_horizontal_lt_one (a := a) (U := U) hy0 hy ht₁.ne hU.le
  have hT := k_horizontal_lt_one (a := a) (U := U) hy0 hy ht₂.ne' hU.le
  have hR := k_vertical_le hy0 (σ := a + U) (by linarith) (t₁ := t₁) (t₂ := t₂) (by linarith)
  rw [abs_of_neg ht₁] at hB
  rw [abs_of_pos ht₂] at hT
  rw [abs_of_pos (by linarith)] at hR
  calc ‖∫ t in t₁..t₂, f (a + t * I)‖
      = ‖(∫ x : ℝ in a..a + U, f (x + t₁ * I)) - (∫ x : ℝ in a..a + U, f (x + t₂ * I)) +
          I • (∫ t : ℝ in t₁..t₂, f ((a + U : ℝ) + t * I))‖ := by rw [hnorm, ← hc]
    _ ≤ ‖∫ x : ℝ in a..a + U, f (x + t₁ * I)‖ + ‖∫ x : ℝ in a..a + U, f (x + t₂ * I)‖ +
          ‖∫ t : ℝ in t₁..t₂, f ((a + U : ℝ) + t * I)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul (I : ℂ), Complex.norm_I, one_mul]
        have := norm_sub_le (∫ x : ℝ in a..a + U, f (x + t₁ * I)) (∫ x : ℝ in a..a + U, f (x + t₂ * I))
        linarith
    _ ≤ y ^ a / (-Real.log y) * (1 / (-t₁)) + y ^ a / (-Real.log y) * (1 / t₂) +
          y ^ (a + U) / (a + U) * (t₂ - t₁) := by
        gcongr
    _ = _ := by ring

/-- (K2) `0 < y < 1`: the truncated integral of `y^s/s` is small. -/
private theorem kernel_lt_one {y a t₁ t₂ : ℝ} (hy0 : 0 < y) (hy : y < 1) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I))‖
      ≤ y ^ a / (2 * π * (-Real.log y)) * (1 / (-t₁) + 1 / t₂) := by
  set C : ℝ := y ^ a / (-Real.log y) * (1 / (-t₁) + 1 / t₂) with hC
  have key : ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖ ≤ C := by
    have hlim : Tendsto (fun U : ℝ => C + y ^ a * (t₂ - t₁) / (a + U)) atTop (𝓝 (C + 0)) := by
      apply Tendsto.const_add
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop a tendsto_id)
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with U hU
    refine (k_lt_one_step hy0 hy ha ht₁ ht₂ hU).trans ?_
    rw [hC]
    gcongr
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hy0 hy.le (by linarith))
      (by linarith)
  rw [norm_mul, k_norm_two_pi]
  calc 1 / (2 * π) * ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖
      ≤ 1 / (2 * π) * C := by gcongr
    _ = _ := by rw [hC]; ring

/-- The `O(1)` condition at the simple pole `0` of `y^s / s` with residue `1`. -/
private theorem k_near_zero {y : ℝ} (hy : 0 < y) :
    ((fun s : ℂ => (y : ℂ) ^ s / s) - fun s => (1 : ℂ) / (s - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
  have hd : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (0 : ℂ) * Complex.log y) 0 :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (by exact_mod_cast hy.ne'))).hasDerivAt
  have hO := hd.isBigO_sub
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨c, hc⟩ := hO
  rw [Asymptotics.isBigO_iff]
  refine ⟨c, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hc] with s hs hs0
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hs0
  simp only [Pi.sub_apply, sub_zero, Pi.one_apply, norm_one, mul_one]
  rw [Complex.cpow_zero, sub_zero] at hs
  rw [div_sub_div_same, norm_div, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  exact hs

/-- (K1), one rectangle: the bound with the left-edge error term. -/
private theorem k_gt_one_step {y a t₁ t₂ U : ℝ} (hy : 1 < y) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) (hU : a < U) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)) - 1‖
      ≤ 1 / (2 * π) * (y ^ a / Real.log y * (1 / (-t₁) + 1 / t₂)
          + y ^ (a - U) * (U - a)⁻¹ * (t₂ - t₁)) := by
  have hy0 : 0 < y := by linarith
  have hres := ResidueTheoremOnRectangleWithSimplePole_prime (f := fun s : ℂ => (y : ℂ) ^ s / s)
    (z := ⟨a - U, t₁⟩) (w := ⟨a, t₂⟩) (p := 0) (A := 1) (by show a - U ≤ a; linarith)
    (by show t₁ ≤ t₂; linarith) ?_ ?_ (k_near_zero hy0)
  rotate_left
  · show Set.uIcc (a - U) a ×ℂ Set.uIcc t₁ t₂ ∈ 𝓝 0
    have hopen : IsOpen (Set.Ioo (a - U) a ×ℂ Set.Ioo t₁ t₂) := isOpen_Ioo.reProdIm isOpen_Ioo
    refine mem_of_superset (hopen.mem_nhds ?_) ?_
    · rw [Complex.mem_reProdIm]
      simp only [Complex.zero_re, Complex.zero_im, Set.mem_Ioo]
      exact ⟨⟨by linarith, ha⟩, ht₁, ht₂⟩
    · intro s hs
      rw [Complex.mem_reProdIm] at hs ⊢
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      exact ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩
  · intro s hs
    apply (k_differentiableAt hy0 _).differentiableWithinAt
    intro h0
    exact hs.2 (by simp [h0])
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at hres
  set B := ∫ x : ℝ in a - U..a, (y : ℂ) ^ ((x : ℂ) + t₁ * I) / ((x : ℂ) + t₁ * I) with hB
  set T := ∫ x : ℝ in a - U..a, (y : ℂ) ^ ((x : ℂ) + t₂ * I) / ((x : ℂ) + t₂ * I) with hT
  set F := ∫ t : ℝ in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I) with hF
  set L := ∫ t : ℝ in t₁..t₂, (y : ℂ) ^ (((a - U : ℝ) : ℂ) + t * I) / (((a - U : ℝ) : ℂ) + t * I)
    with hL
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [one_div, inv_mul_eq_iff_eq_mul₀ hne, mul_one] at hres
  have h3 : F = 2 * π + I * B - I * T + L := by
    linear_combination (-I) * hres + (F - L - 2 * π) * Complex.I_mul_I
  have h4 : (1 / (2 * π) : ℂ) * F - 1 = (1 / (2 * π) : ℂ) * (I * B - I * T + L) := by
    rw [h3]
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  rw [h4, norm_mul, k_norm_two_pi]
  have hBle := k_horizontal_gt_one (a := a) (U := U) hy ht₁.ne (by linarith)
  have hTle := k_horizontal_gt_one (a := a) (U := U) hy ht₂.ne' (by linarith)
  have hLle := k_vertical_le hy0 (σ := a - U) (by linarith) (t₁ := t₁) (t₂ := t₂) (by linarith)
  rw [abs_of_neg ht₁] at hBle
  rw [abs_of_pos ht₂] at hTle
  rw [abs_of_neg (by linarith), neg_sub] at hLle
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖I * B - I * T + L‖ ≤ ‖I * B‖ + ‖I * T‖ + ‖L‖ := by
        refine (norm_add_le _ _).trans ?_
        have := norm_sub_le (I * B) (I * T)
        linarith
    _ = ‖B‖ + ‖T‖ + ‖L‖ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    _ ≤ y ^ a / Real.log y * (1 / (-t₁)) + y ^ a / Real.log y * (1 / t₂)
          + y ^ (a - U) / (U - a) * (t₂ - t₁) := by
        gcongr
    _ = _ := by ring

/-- (K1) `y > 1`: the truncated integral of `y^s/s` over `Re s = a > 0`, `Im s ∈ [t₁, t₂]`
with `t₁ < 0 < t₂`, is `1` up to the horizontal-segment error. -/
private theorem kernel_gt_one {y a t₁ t₂ : ℝ} (hy : 1 < y) (ha : 0 < a) (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)) - 1‖
      ≤ y ^ a / (2 * π * Real.log y) * (1 / (-t₁) + 1 / t₂) := by
  set C : ℝ := y ^ a / Real.log y * (1 / (-t₁) + 1 / t₂) with hC
  have h1 : Tendsto (fun U : ℝ => y ^ (a - U)) atTop (𝓝 0) := by
    have := (tendsto_rpow_atBot_of_base_gt_one y hy).comp
      (tendsto_atBot_add_const_left atTop a tendsto_neg_atTop_atBot)
    refine this.congr fun U => ?_
    simp [Function.comp, sub_eq_add_neg]
  have h2 : Tendsto (fun U : ℝ => (U - a)⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-a) tendsto_id)
    refine this.congr fun U => ?_
    simp [Function.comp, sub_eq_add_neg]
  have hlim : Tendsto (fun U : ℝ => 1 / (2 * π) * (C + y ^ (a - U) * (U - a)⁻¹ * (t₂ - t₁)))
      atTop (𝓝 (1 / (2 * π) * (C + 0 * 0 * (t₂ - t₁)))) :=
    ((h1.mul h2).mul_const _).const_add C |>.const_mul _
  simp only [zero_mul, add_zero] at hlim
  have key := ge_of_tendsto hlim ((eventually_gt_atTop a).mono fun U hU =>
    k_gt_one_step hy ha ht₁ ht₂ hU)
  refine key.trans (le_of_eq ?_)
  rw [hC]
  ring


/-! ### Piece `Shift` -/

/-! ## (A) Absorption -/

private theorem absorb {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u ^ 2) ^ 2 * Real.exp (-κ * u) ≤ C * Real.exp (-(κ / 2) * u) := by
  refine ⟨3 * (1 + 24 * (2 / κ) ^ 4), by positivity, fun u hu => ?_⟩
  have h1 : (1 + u ^ 2) ^ 2 ≤ 3 * (1 + u ^ 4) := by nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hku : 0 ≤ κ * u / 2 := by positivity
  have h2 : (κ * u / 2) ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp (κ * u / 2) :=
    Real.pow_div_factorial_le_exp _ hku 4
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h2
  have h3 : u ^ 4 = (2 / κ) ^ 4 * (κ * u / 2) ^ 4 := by
    field_simp
  have h4 : u ^ 4 ≤ 24 * (2 / κ) ^ 4 * Real.exp (κ * u / 2) := by
    rw [h3]
    have : (κ * u / 2) ^ 4 ≤ 24 * Real.exp (κ * u / 2) := by linarith
    have hp : 0 ≤ (2 / κ) ^ 4 := by positivity
    nlinarith
  have hexp1 : 1 ≤ Real.exp (κ * u / 2) := Real.one_le_exp (by positivity)
  have h5 : (1 + u ^ 2) ^ 2 ≤ 3 * (1 + 24 * (2 / κ) ^ 4) * Real.exp (κ * u / 2) := by
    have hp : 0 ≤ (2 / κ) ^ 4 := by positivity
    nlinarith
  have hsplit : Real.exp (-κ * u) = Real.exp (-(κ / 2) * u) * Real.exp (-(κ / 2) * u) := by
    rw [← Real.exp_add]; ring_nf
  have hexp2 : Real.exp (κ * u / 2) * Real.exp (-(κ / 2) * u) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpos : 0 ≤ Real.exp (-(κ / 2) * u) := Real.exp_nonneg _
  calc (1 + u ^ 2) ^ 2 * Real.exp (-κ * u)
      = (1 + u ^ 2) ^ 2 * Real.exp (-(κ / 2) * u) * Real.exp (-(κ / 2) * u) := by
        rw [hsplit]; ring
    _ ≤ 3 * (1 + 24 * (2 / κ) ^ 4) * Real.exp (κ * u / 2) * Real.exp (-(κ / 2) * u)
          * Real.exp (-(κ / 2) * u) := by
        gcongr
    _ = 3 * (1 + 24 * (2 / κ) ^ 4) * Real.exp (-(κ / 2) * u) := by
        rw [mul_assoc (3 * (1 + 24 * (2 / κ) ^ 4)), hexp2]; ring

/-! ## (B) Removable singularities -/

private theorem exists_extension_of_finite {U : Set ℂ} (hU : IsOpen U) (P : Finset ℂ) {H : ℂ → ℂ}
    {B : ℝ} (hH : DifferentiableOn ℂ H (U \ (P : Set ℂ))) (hB : ∀ z ∈ U \ (P : Set ℂ), ‖H z‖ ≤ B) :
    ∃ H' : ℂ → ℂ, DifferentiableOn ℂ H' U ∧ (∀ z ∈ U \ (P : Set ℂ), H' z = H z) ∧
      ∀ z ∈ U, ‖H' z‖ ≤ B := by
  induction P using Finset.induction_on generalizing U with
  | empty =>
    simp only [Finset.coe_empty, diff_empty] at hH hB
    exact ⟨H, hH, fun z _ => rfl, hB⟩
  | insert p P hp ih =>
    have hset : (U \ {p}) \ (P : Set ℂ) = U \ ((insert p P : Finset ℂ) : Set ℂ) := by
      rw [Finset.coe_insert, diff_diff, singleton_union]
    have hU' : IsOpen (U \ {p}) := hU.sdiff isClosed_singleton
    obtain ⟨H₁, hH₁, hH₁eq, hH₁B⟩ := ih hU' (by rw [hset]; exact hH) (by rw [hset]; exact hB)
    rw [hset] at hH₁eq
    by_cases hpU : p ∈ U
    · have hc : U ∈ 𝓝 p := hU.mem_nhds hpU
      have hbdd : BddAbove (norm ∘ H₁ '' (U \ {p})) := by
        refine ⟨B, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        exact hH₁B z hz
      set L := limUnder (𝓝[≠] p) H₁ with hL
      have hH₂ : DifferentiableOn ℂ (Function.update H₁ p L) U :=
        Complex.differentiableOn_update_limUnder_of_bddAbove hc hH₁ hbdd
      refine ⟨Function.update H₁ p L, hH₂, ?_, ?_⟩
      · intro z hz
        have hzp : z ≠ p := by
          intro h; subst h
          exact hz.2 (by simp)
        rw [Function.update_of_ne hzp]
        exact hH₁eq z hz
      · intro z hz
        by_cases hzp : z = p
        · subst hzp
          -- continuity at z
          have hcont : ContinuousAt (Function.update H₁ z L) z :=
            (hH₂.differentiableAt hc).continuousAt
          have ht : Tendsto (Function.update H₁ z L) (𝓝[≠] z)
              (𝓝 (Function.update H₁ z L z)) :=
            hcont.tendsto.mono_left nhdsWithin_le_nhds
          have ht' : Tendsto H₁ (𝓝[≠] z) (𝓝 (Function.update H₁ z L z)) := by
            refine ht.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with w hw
            exact Function.update_of_ne hw _ _
          have hev : ∀ᶠ w in 𝓝[≠] z, ‖H₁ w‖ ≤ B := by
            have : U \ {z} ∈ 𝓝[≠] z := diff_mem_nhdsWithin_compl hc {z}
            filter_upwards [this] with w hw
            exact hH₁B w hw
          exact le_of_tendsto ht'.norm hev
        · rw [Function.update_of_ne hzp]
          exact hH₁B z ⟨hz, hzp⟩
    · have hUeq : U \ {p} = U := by
        ext z; simp only [mem_diff, mem_singleton_iff, and_iff_left_iff_imp]
        rintro hz rfl; exact hpU hz
      rw [hUeq] at hH₁ hH₁B
      exact ⟨H₁, hH₁, hH₁eq, hH₁B⟩

/-! ## (E) Contour shift -/

private lemma e_cont_max {σ₁ : ℝ} (hσ₁ : 0 < σ₁) : Continuous (fun t : ℝ => 1 / max σ₁ |t|) := by
  apply Continuous.div continuous_const (continuous_const.max continuous_abs)
  intro t; exact (lt_max_of_lt_left hσ₁).ne'

/-- `∫_{-T}^{T} dt / max σ₁ |t| = 2 + 2 log (T/σ₁)`. -/
private lemma e_integral_max {σ₁ T : ℝ} (hσ₁ : 0 < σ₁) (hσ₁T : σ₁ ≤ T) :
    ∫ t in (-T)..T, 1 / max σ₁ |t| = 2 + 2 * Real.log (T / σ₁) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => 1 / max σ₁ |t|) volume a b :=
    fun a b => (e_cont_max hσ₁).intervalIntegrable a b
  have h1 : ∫ t in (-T)..(-σ₁), 1 / max σ₁ |t| = Real.log (T / σ₁) := by
    have : ∫ t in (-T)..(-σ₁), 1 / max σ₁ |t| = ∫ t in (-T)..(-σ₁), (fun t : ℝ => t⁻¹) (-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [abs_of_neg (by linarith [ht.2]), max_eq_right (by linarith [ht.2]), one_div]
    rw [this, intervalIntegral.integral_comp_neg, neg_neg, neg_neg,
      integral_inv_of_pos hσ₁ (by linarith)]
  have h2 : ∫ t in (-σ₁)..σ₁, 1 / max σ₁ |t| = 2 := by
    have : ∫ t in (-σ₁)..σ₁, 1 / max σ₁ |t| = ∫ t in (-σ₁)..σ₁, (1 / σ₁) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [max_eq_left (abs_le.mpr ⟨ht.1, ht.2⟩)]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  have h3 : ∫ t in σ₁..T, 1 / max σ₁ |t| = Real.log (T / σ₁) := by
    have : ∫ t in σ₁..T, 1 / max σ₁ |t| = ∫ t in σ₁..T, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hσ₁T] at ht
      simp only
      rw [abs_of_pos (by linarith [ht.1]), max_eq_right ht.1, one_div]
    rw [this, integral_inv_of_pos hσ₁ (by linarith)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-T) (-σ₁)) (hint (-σ₁) T),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-σ₁) σ₁) (hint σ₁ T), h1, h2, h3]
  ring

private lemma e_norm_term {H : ℂ → ℂ} {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖H s * (x : ℂ) ^ s / s‖ = ‖H s‖ * x ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- Horizontal edge bound. -/
private lemma e_horiz {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T)
    (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) {t : ℝ} (ht : |t| = T) :
    ‖∫ σ in σ₁..σ₀, H ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ B * x ^ σ₀ / T * (σ₀ - σ₁) := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₁) (b := σ₀)
    (C := B * x ^ σ₀ / T)
    (f := fun σ : ℝ => H ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) ?_
  · rwa [abs_of_nonneg (by linarith)] at this
  · intro σ hσ'
    rw [Set.uIoc_of_le hσ] at hσ'
    have hσI : σ ∈ Icc σ₁ σ₀ := ⟨hσ'.1.le, hσ'.2⟩
    have htI : t ∈ Icc (-T) T := abs_le.mp ht.le
    have hmem : (σ : ℂ) + t * I ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simpa using ⟨hσI, htI⟩
    have hnorm : T ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
      simpa [ht] using this
    rw [e_norm_term hx0]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    have hxσ : x ^ σ ≤ x ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hx hσI.2
    exact div_le_div₀ (by positivity) (mul_le_mul (hHB _ hmem) hxσ (by positivity) hB) hT0 hnorm

/-- Left edge bound. -/
private lemma e_left {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T)
    (hx : 1 ≤ x) (hB : 0 ≤ B) (hσ₁T : σ₁ ≤ T)
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) :
    ‖∫ t in (-T)..T, H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I)‖
      ≤ B * x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) := by
  have hx0 : 0 < x := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -T) (b := T)
    (by linarith)
    (g := fun t : ℝ => B * x ^ σ₁ * (1 / max σ₁ |t|))
    (f := fun t : ℝ => H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I))
    ?_ ?_
  · rw [intervalIntegral.integral_const_mul, e_integral_max hσ₁ hσ₁T] at hbound
    exact hbound
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htI : t ∈ Icc (-T) T := ⟨ht.1.le, ht.2⟩
    have hmem : (σ₁ : ℂ) + t * I ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, zero_add, mul_im]
      exact ⟨⟨le_refl σ₁, hσ⟩, htI⟩
    have hnorm : max σ₁ |t| ≤ ‖(σ₁ : ℂ) + t * I‖ := by
      refine max_le ?_ ?_
      · have := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I)
        simpa [abs_of_pos hσ₁] using this
      · have := Complex.abs_im_le_norm ((σ₁ : ℂ) + t * I)
        simpa using this
    rw [e_norm_term hx0]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    rw [mul_one_div]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (hHB _ hmem) (by positivity))
      (lt_max_of_lt_left hσ₁) hnorm
  · exact (continuous_const.mul (e_cont_max hσ₁)).intervalIntegrable _ _

private theorem shift_bound {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ ≤ 1)
    (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hH : DifferentiableOn ℂ H (Icc σ₁ σ₀ ×ℂ Icc (-T) T))
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) :
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        H ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖
      ≤ B / (2 * π) * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + 2 * (σ₀ - σ₁) * x ^ σ₀ / T) := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hσ₁T : σ₁ ≤ T := hσ₁1.trans hT
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => H s * (x : ℂ) ^ s / s)
      (Icc σ₁ σ₀ ×ℂ Icc (-T) T) := by
    apply DifferentiableOn.div
      (hH.mul (differentiableOn_id.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))))
      differentiableOn_id
    intro s hs h0
    simp only [id] at h0
    rw [Complex.mem_reProdIm, h0] at hs
    simp only [zero_re, zero_im, Set.mem_Icc] at hs
    linarith [hs.1.1]
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s : ℂ => H s * (x : ℂ) ^ s / s) ⟨σ₁, -T⟩ ⟨σ₀, T⟩ (by
      dsimp only
      rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by linarith)]
      exact hdiff)
  dsimp only at hc
  rw [smul_eq_mul, smul_eq_mul] at hc
  set V₀ := ∫ t in (-T)..T,
    H ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) with hV₀
  set V₁ := ∫ t in (-T)..T,
    H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I) with hV₁
  set bot := ∫ σ in σ₁..σ₀,
    H ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) * (x : ℂ) ^ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
      / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) with hbot
  set top := ∫ σ in σ₁..σ₀,
    H ((σ : ℂ) + (T : ℂ) * I) * (x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)
      / ((σ : ℂ) + (T : ℂ) * I) with htop
  have hV : I * V₀ = I * V₁ - bot + top := by linear_combination hc
  have hV0 : ‖V₀‖ ≤ ‖V₁‖ + ‖bot‖ + ‖top‖ := by
    have h1 : ‖V₀‖ = ‖I * V₀‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [h1, hV]
    calc ‖I * V₁ - bot + top‖ ≤ ‖I * V₁ - bot‖ + ‖top‖ := norm_add_le _ _
      _ ≤ ‖I * V₁‖ + ‖bot‖ + ‖top‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖V₁‖ + ‖bot‖ + ‖top‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hleft := e_left hσ₁ hσ hT hx hB hσ₁T hHB
  have hbot' := e_horiz hσ hT hx hB hHB (t := -T) (by rw [abs_neg, abs_of_pos hT0])
  have htop' := e_horiz hσ hT hx hB hHB (t := T) (abs_of_pos hT0)
  have hnorm : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnorm]
  have hfinal : ‖V₀‖ ≤ B * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁))
      + 2 * (σ₀ - σ₁) * x ^ σ₀ / T) := by
    calc ‖V₀‖ ≤ ‖V₁‖ + ‖bot‖ + ‖top‖ := hV0
      _ ≤ B * x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + B * x ^ σ₀ / T * (σ₀ - σ₁)
          + B * x ^ σ₀ / T * (σ₀ - σ₁) := add_le_add (add_le_add hleft hbot') htop'
      _ = _ := by ring
  calc 1 / (2 * π) * ‖V₀‖
      ≤ 1 / (2 * π) * (B * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁))
          + 2 * (σ₀ - σ₁) * x ^ σ₀ / T)) := by gcongr
    _ = _ := by ring


/-! ### Piece `PerronFormula` -/

/-! ### Elementary facts about `s t = σ₀ + t I` -/

private lemma c_s_re (σ₀ t : ℝ) : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp

private lemma c_s_ne_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (t : ℝ) : (σ₀ : ℂ) + t * I ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  linarith

private lemma c_le_norm_s {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (t : ℝ) : σ₀ ≤ ‖(σ₀ : ℂ) + t * I‖ := by
  have h := Complex.abs_re_le_norm ((σ₀ : ℂ) + t * I)
  rwa [c_s_re, abs_of_pos hσ₀] at h

/-! ### Summability of the Dirichlet series -/

private lemma c_norm_term_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (σ₀ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ₀ : ℂ) + t * I) n‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ := by
  rw [LSeries.norm_term_eq, c_s_re]
  split_ifs with hn
  · subst hn
    simp
  · gcongr
    exact ha n

private lemma c_summable {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (t : ℝ) : LSeriesSummable a ((σ₀ : ℂ) + t * I) :=
  Summable.of_norm_bounded (summable_vonMangoldt_div_rpow hσ₀) (c_norm_term_le ha σ₀ t)

private lemma c_norm_F_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {x σ₀ : ℝ} (hx : 0 < x) (hσ₀ : 0 < σ₀) (t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ * x ^ σ₀ / σ₀ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, c_s_re]
  have h1 := c_norm_term_le ha σ₀ t n
  have h2 := c_le_norm_s hσ₀ t
  have h3 : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx.le _
  have h4 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact div_le_div₀ (mul_nonneg h4 h3) (mul_le_mul_of_nonneg_right h1 h3) hσ₀ h2

private lemma c_continuous_F (a : ℕ → ℂ) {x σ₀ : ℝ} (hx : 0 < x) (hσ₀ : 0 < σ₀) (n : ℕ) :
    Continuous fun t : ℝ =>
      LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := by
  have hs : Continuous fun t : ℝ => (σ₀ : ℂ) + t * I := by fun_prop
  have hx' : Continuous fun t : ℝ => (x : ℂ) ^ ((σ₀ : ℂ) + t * I) :=
    hs.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, zero_mul, zero_div]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hn' : Continuous fun t : ℝ => (n : ℂ) ^ ((σ₀ : ℂ) + t * I) :=
      hs.const_cpow (Or.inl hn0)
    refine ((continuous_const.div hn' ?_).mul hx').div hs (c_s_ne_zero hσ₀)
    intro t
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (c_s_ne_zero hσ₀ t)]
    exact hn0

/-! ### Termwise evaluation -/

private lemma c_div_cpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx hn0,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow, div_eq_mul_inv]
  rw [Complex.natCast_arg]
  exact Real.pi_pos.ne

private lemma c_integral_term (a : ℕ → ℂ) {x σ₀ T : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (∫ t in (-T)..T, LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) /
        ((σ₀ : ℂ) + t * I))
      = a n * ∫ t in (-T)..T, ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [LSeries.term_of_ne_zero hn, c_div_cpow hx n]
  ring

/-! ### The per-term bound -/

private lemma c_term_bound {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      - (if n < N then a n else 0)‖
      ≤ 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
          |Real.log (x / n)|) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hσ₀' : 0 < σ₀ := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  rcases eq_or_ne n 0 with rfl | hn
  · -- the `n = 0` term
    have ha0 : a 0 = 0 := by
      have h := ha 0
      simp at h
      exact h
    simp [ha0]
  · rw [c_integral_term a hx0.le hn]
    have hy0 : 0 < x / n := div_pos hx0 (by positivity)
    have hyσ : 0 ≤ (x / n) ^ σ₀ := Real.rpow_nonneg hy0.le _
    by_cases hnN : n < N
    · -- `n < N`, so `y = x / n > 1`
      rw [if_pos hnN]
      have hn1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
      have hy : 1 < x / n := by
        rw [lt_div_iff₀ (by positivity), hx]; linarith
      have hK := kernel_gt_one hy hσ₀' (neg_neg_of_pos hT) hT
      have hlog : 0 < Real.log (x / n) := Real.log_pos hy
      have heq : (1 / (2 * π) : ℂ) * (a n * ∫ t in (-T)..T,
          ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - a n
          = a n * ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
          ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - 1) := by ring
      rw [heq, norm_mul]
      calc ‖a n‖ * ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
              ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - 1‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((x / n) ^ σ₀ / (2 * π * Real.log (x / n)) * (1 / (- -T) + 1 / T)) :=
            mul_le_mul (ha n) hK (norm_nonneg _) hΛ
        _ = 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
              |Real.log (x / n)|) := by
            rw [abs_of_pos hlog, neg_neg]
            field_simp
            ring
    · -- `n ≥ N`, so `y = x / n < 1`
      rw [if_neg hnN, sub_zero]
      have hn1 : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_lt hnN
      have hy : x / n < 1 := by
        rw [div_lt_iff₀ (by positivity), hx]; linarith
      have hK := kernel_lt_one hy0 hy hσ₀' (neg_neg_of_pos hT) hT
      have hlog : Real.log (x / n) < 0 := Real.log_neg hy0 hy
      rw [mul_left_comm, norm_mul]
      calc ‖a n‖ * ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
              ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((x / n) ^ σ₀ / (2 * π * (-Real.log (x / n))) * (1 / (- -T) + 1 / T)) :=
            mul_le_mul (ha n) hK (norm_nonneg _) hΛ
        _ = 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
              |Real.log (x / n)|) := by
            rw [abs_of_neg hlog, neg_neg]
            have : 0 < -Real.log (x / n) := by linarith
            field_simp
            ring

/-! ### The truncated Perron formula -/

private theorem perron_truncated {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    {T : ℝ} (hT : 0 < T) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      - ∑ n ∈ Finset.range N, a n‖
      ≤ 1 / (π * T) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
          |Real.log (x / n)| := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hσ₀' : 0 < σ₀ := by linarith
  -- Step 1: interchange sum and integral
  have hDCT : HasSum
      (fun n : ℕ => ∫ t in (-T)..T,
        LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ * x ^ σ₀ / σ₀)
    · intro n
      exact (c_continuous_F a hx0 hσ₀' n).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun t _ => c_norm_F_le ha hx0 hσ₀' t n)
    · exact Filter.Eventually.of_forall
        (fun t _ => ((summable_vonMangoldt_div_rpow hσ₀).mul_right _).div_const _)
    · exact _root_.intervalIntegrable_const
    · exact Filter.Eventually.of_forall
        (fun t _ => ((c_summable ha hσ₀ t).hasSum.mul_right _).div_const _)
  -- Step 2: the sequences
  set u : ℕ → ℂ := fun n => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
    LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)
    with hu_def
  set v : ℕ → ℂ := fun n => if n < N then a n else 0 with hv_def
  set w : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
    |Real.log (x / n)| with hw_def
  have hbound : ∀ n, ‖u n - v n‖ ≤ 1 / (π * T) * w n :=
    fun n => c_term_bound ha hN hx hσ₀ hT n
  have hw : Summable (fun n => 1 / (π * T) * w n) :=
    (summable_perron_error hN hx hσ₀).mul_left _
  have hnorm : Summable (fun n => ‖u n - v n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hw
  have hu : Summable u := hDCT.summable.mul_left _
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range] at hn
    simp [hv_def, hn]
  have h1 : (1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
      LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      = ∑' n, u n := by
    rw [← hDCT.tsum_eq, hu_def, tsum_mul_left]
  have h2 : ∑ n ∈ Finset.range N, a n = ∑' n, v n := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      simp [hv_def, hn]
    · intro n hn
      rw [Finset.mem_range] at hn
      simp [hv_def, hn]
  rw [h1, h2, ← hu.tsum_sub hv]
  calc ‖∑' n, (u n - v n)‖
      ≤ ∑' n, ‖u n - v n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, 1 / (π * T) * w n := hnorm.tsum_le_tsum hbound hw
    _ = 1 / (π * T) * ∑' n, w n := tsum_mul_left


/-! ### Piece `Polar` -/

/-! ## Numeric facts -/

private lemma d_log_two_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_div, Real.log_inv] at h
  linarith

private lemma d_log_two_le : Real.log 2 ≤ 3 / 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 8)
  have : Real.exp (3 / 4) = Real.exp (3 / 8) * Real.exp (3 / 8) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith [Real.exp_pos (3 / 8)]

private lemma d_log_three_le : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith

private lemma d_log_x_ge {x : ℝ} (hx : 3 / 2 ≤ x) : 1 / 3 ≤ Real.log x := by
  have h1 : Real.log (3 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
  have : Real.log (2 / 3) = - Real.log (3 / 2) := by
    rw [← Real.log_inv]; norm_num
  linarith

private lemma d_norm_two_pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
  simp [Real.pi_pos.le]

/-! ## Elementary complex facts -/

private lemma d_p_ne_zero {p : ℂ} (hp1 : 1 / 2 ≤ p.re) : p ≠ 0 := by
  intro h
  rw [h, Complex.zero_re] at hp1
  norm_num at hp1

private lemma d_re (a t : ℝ) : ((a : ℂ) + t * I).re = a := by simp

private lemma d_s_ne_zero {a : ℝ} (ha : 0 < a) (t : ℝ) : (a : ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

private lemma d_norm_s_ge_re (a t : ℝ) : |a| ≤ ‖(a : ℂ) + t * I‖ := by
  have := Complex.abs_re_le_norm ((a : ℂ) + t * I); simpa using this

private lemma d_norm_s_ge_im (a t : ℝ) : |t| ≤ ‖(a : ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm ((a : ℂ) + t * I); simpa using this

private lemma d_sp_ne_zero {a : ℝ} {p : ℂ} (h : p.re < a) (t : ℝ) : (a : ℂ) + t * I - p ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this; linarith

private lemma d_norm_sp_ge_re (a t : ℝ) (p : ℂ) : |a - p.re| ≤ ‖(a : ℂ) + t * I - p‖ := by
  have := Complex.abs_re_le_norm ((a : ℂ) + t * I - p); simpa using this

private lemma d_norm_sp_ge_im (a t : ℝ) (p : ℂ) : |t - p.im| ≤ ‖(a : ℂ) + t * I - p‖ := by
  have := Complex.abs_im_le_norm ((a : ℂ) + t * I - p); simpa using this

/-! ## Continuity facts -/

private lemma d_cont_s (a : ℝ) : Continuous fun t : ℝ => (a : ℂ) + t * I := by fun_prop

private lemma d_cont_integrand {x a : ℝ} (hx : 0 < x) (ha : 0 < a) {p : ℂ} (hp : p.re < a) :
    Continuous fun t : ℝ =>
      (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)) := by
  apply Continuous.div
  · exact (d_cont_s a).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · fun_prop
  · intro t
    exact mul_ne_zero (d_s_ne_zero ha t) (d_sp_ne_zero hp t)

private lemma d_cont_f₁ {x a : ℝ} (hx : 0 < x) {p : ℂ} (hp : p.re < a) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I - p) := by
  apply Continuous.div
  · exact (d_cont_s a).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · fun_prop
  · intro t
    exact d_sp_ne_zero hp t

private lemma d_cont_f₂ {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I) := by
  apply Continuous.div
  · exact (d_cont_s a).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · fun_prop
  · intro t
    exact d_s_ne_zero ha t

private lemma d_cont_one_div_norm_s {a : ℝ} (ha : 0 < a) :
    Continuous fun t : ℝ => 1 / ‖(a : ℂ) + t * I‖ := by
  apply Continuous.div continuous_const (d_cont_s a).norm
  intro t
  exact norm_ne_zero_iff.mpr (d_s_ne_zero ha t)

private lemma d_cont_one_div_norm_sp {a : ℝ} {p : ℂ} (hp : p.re < a) :
    Continuous fun t : ℝ => 1 / ‖(a : ℂ) + t * I - p‖ := by
  apply Continuous.div continuous_const ((d_cont_s a).sub continuous_const).norm
  intro t
  exact norm_ne_zero_iff.mpr (d_sp_ne_zero hp t)

private lemma d_cont_one_div_max {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Continuous fun u : ℝ => 1 / max δ |u - c| := by
  apply Continuous.div continuous_const (by fun_prop)
  intro u; exact ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _))

private lemma d_cont_one_div_max' {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun u : ℝ => 1 / max δ |u| := by
  simpa using d_cont_one_div_max hδ 0

/-! ## The model integral `∫_{-R}^{R} du / max δ |u|` -/

private lemma d_integral_one_div_max {δ R : ℝ} (hδ : 0 < δ) (hR : δ ≤ R) :
    ∫ u in (-R)..R, 1 / max δ |u| = 2 + 2 * Real.log (R / δ) := by
  have hc := d_cont_one_div_max' hδ
  have h1 : ∫ u in (-R)..(-δ), 1 / max δ |u| = Real.log (R / δ) := by
    have : ∫ u in (-R)..(-δ), 1 / max δ |u| = ∫ u in (-R)..(-δ), (fun v : ℝ => v⁻¹) (-u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      obtain ⟨hu1, hu2⟩ := hu
      simp only
      rw [abs_of_neg (by linarith), max_eq_right (by linarith), one_div]
    rw [this, intervalIntegral.integral_comp_neg (fun v : ℝ => v⁻¹), neg_neg, neg_neg]
    rw [integral_inv]
    rw [Set.uIcc_of_le hR]
    intro h; linarith [h.1]
  have h2 : ∫ u in (-δ)..δ, 1 / max δ |u| = 2 := by
    have : ∫ u in (-δ)..δ, 1 / max δ |u| = ∫ u in (-δ)..δ, (1 / δ : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      simp only
      rw [max_eq_left (abs_le.mpr ⟨hu.1, hu.2⟩)]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  have h3 : ∫ u in δ..R, 1 / max δ |u| = Real.log (R / δ) := by
    have : ∫ u in δ..R, 1 / max δ |u| = ∫ u in δ..R, u⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hR] at hu
      simp only
      rw [abs_of_pos (by linarith [hu.1]), max_eq_right hu.1, one_div]
    rw [this, integral_inv]
    rw [Set.uIcc_of_le hR]
    intro h; linarith [h.1]
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => 1 / max δ |u|) volume a b :=
    fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-R) (-δ)) (hi (-δ) R),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-δ) δ) (hi δ R), h1, h2, h3]
  ring

/-! ## Bounds on `∫ dt/‖s‖` and `∫ dt/‖s - p‖` -/

private lemma d_B_bound {a T : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T) :
    ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I‖ ≤ 2 + 2 * Real.log T := by
  have h := d_integral_one_div_max (δ := 1) (R := T) one_pos hT
  rw [div_one] at h
  rw [← h]
  apply intervalIntegral.integral_mono_on (by linarith)
    ((d_cont_one_div_norm_s (by linarith)).intervalIntegrable _ _)
    ((d_cont_one_div_max' one_pos).intervalIntegrable _ _)
  intro t _
  apply one_div_le_one_div_of_le (lt_of_lt_of_le one_pos (le_max_left _ _))
  apply max_le
  · calc (1 : ℝ) ≤ a := ha
      _ = |a| := (abs_of_pos (by linarith)).symm
      _ ≤ _ := d_norm_s_ge_re a t
  · exact d_norm_s_ge_im a t

private lemma d_A_bound {a T : ℝ} {p : ℂ} (ha : 1 < a) (hT : 2 ≤ T) (hpa : p.re ≤ 1) :
    ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖ ≤ 2 + 2 * Real.log (3 * T / min (a - 1) 1) := by
  set δ := min (a - 1) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδa : δ ≤ a - 1 := min_le_left _ _
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log (3 * T / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hcont := d_cont_one_div_norm_sp (p := p) (a := a) (by linarith)
  by_cases h2 : 2 * T ≤ |p.im|
  · have : ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖ ≤ ∫ t in (-T)..T, (1 / T : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        _root_.intervalIntegrable_const
      intro t ht
      apply one_div_le_one_div_of_le hT0
      refine le_trans ?_ (d_norm_sp_ge_im a t p)
      have ht' : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
      calc T ≤ |p.im| - |t| := by linarith
        _ ≤ |t - p.im| := by
          rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc _ ≤ (T - -T) * (1 / T) := this
      _ = 2 := by field_simp; ring
      _ ≤ _ := by linarith
  · push Not at h2
    have step1 : ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖
        ≤ ∫ t in (-T)..T, 1 / max δ |t - p.im| := by
      apply intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        ((d_cont_one_div_max hδ0 p.im).intervalIntegrable _ _)
      intro t _
      apply one_div_le_one_div_of_le (lt_of_lt_of_le hδ0 (le_max_left _ _))
      apply max_le
      · calc δ ≤ a - 1 := hδa
          _ ≤ a - p.re := by linarith
          _ ≤ |a - p.re| := le_abs_self _
          _ ≤ _ := d_norm_sp_ge_re a t p
      · exact d_norm_sp_ge_im a t p
    have step2 : ∫ t in (-T)..T, 1 / max δ |t - p.im|
        = ∫ u in (-T - p.im)..(T - p.im), 1 / max δ |u| :=
      intervalIntegral.integral_comp_sub_right (fun u => 1 / max δ |u|) p.im
    have step3 : ∫ u in (-T - p.im)..(T - p.im), 1 / max δ |u|
        ≤ ∫ u in (-(3 * T))..(3 * T), 1 / max δ |u| := by
      have hγ' := abs_lt.mp h2
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      · exact Filter.Eventually.of_forall (fun u => by positivity)
      · exact (d_cont_one_div_max' hδ0).intervalIntegrable _ _
    have step4 := d_integral_one_div_max hδ0 (by linarith : δ ≤ 3 * T)
    rw [step4] at step3
    linarith

/-! ## Case 1: `|Im p| ≤ T/2` -/

private lemma d_case1 {p : ℂ} (hp1 : 1 / 2 ≤ p.re) (hp2 : p.re ≤ 1) {x a T : ℝ}
    (hx : 3 / 2 ≤ x) (ha : 1 < a) (hT : 2 ≤ T) (hγ : |p.im| ≤ T / 2) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p‖ ≤ 2 + 6 * x ^ a / T := by
  have hp0 : p ≠ 0 := d_p_ne_zero hp1
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have ha0 : 0 < a := by linarith
  have hpa : p.re < a := by linarith
  have hT0 : 0 < T := by linarith
  have hlogx : 1 / 3 ≤ Real.log x := d_log_x_ge hx
  have hγ' := abs_le.mp hγ
  -- the two kernels
  set f₁ : ℝ → ℂ := fun t => (x : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I - p) with hf₁
  set f₂ : ℝ → ℂ := fun t => (x : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I) with hf₂
  have hf₁c : Continuous f₁ := d_cont_f₁ hx0 hpa
  have hf₂c : Continuous f₂ := d_cont_f₂ hx0 ha0
  -- partial fractions
  have hsplit : (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      = (1 / p) * ((∫ t in (-T)..T, f₁ t) - ∫ t in (-T)..T, f₂ t) := by
    rw [← intervalIntegral.integral_sub (hf₁c.intervalIntegrable _ _)
      (hf₂c.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hf₁, hf₂]
    have h1 := d_s_ne_zero ha0 t
    have h2 := d_sp_ne_zero hpa t
    field_simp
    ring
  -- J₀
  have hJ0 := kernel_gt_one (y := x) (a := a) (t₁ := -T) (t₂ := T) hx1 ha0 (by linarith) hT0
  -- J_p via the shift `t = u + Im p`
  set g : ℝ → ℂ := fun u =>
    (x : ℂ) ^ (((a - p.re : ℝ) : ℂ) + u * I) / (((a - p.re : ℝ) : ℂ) + u * I) with hg
  have hshift : (∫ t in (-T)..T, f₁ t)
      = (x : ℂ) ^ p * ∫ u in (-T - p.im)..(T - p.im), g u := by
    have h := intervalIntegral.integral_comp_add_right f₁ p.im (a := -T - p.im) (b := T - p.im)
    simp only [sub_add_cancel] at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [hf₁, hg]
    have e1 : (a : ℂ) + ((u + p.im : ℝ) : ℂ) * I - p = ((a - p.re : ℝ) : ℂ) + u * I := by
      apply Complex.ext <;> simp
    have e2 : (a : ℂ) + ((u + p.im : ℝ) : ℂ) * I = p + (((a - p.re : ℝ) : ℂ) + u * I) := by
      apply Complex.ext <;> simp
      ring
    rw [e1, e2, Complex.cpow_add _ _ hxc, mul_div_assoc]
  have hJp := kernel_gt_one (y := x) (a := a - p.re) (t₁ := -T - p.im) (t₂ := T - p.im) hx1
    (by linarith) (by linarith) (by linarith)
  -- assemble
  have hI : (1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p
      = (1 / p) * ((x : ℂ) ^ p *
          ((1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1)
          - ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T, f₂ t) - 1)) - 1 / p := by
    rw [hsplit, hshift]; ring
  rw [hI]
  -- positivity of the constant
  have hc0 : 0 ≤ x ^ a / (2 * π * Real.log x) := by
    apply div_nonneg (Real.rpow_nonneg hx0.le _)
    have := Real.pi_pos
    positivity
  have hcab : 0 ≤ x ^ (a - p.re) / (2 * π * Real.log x) := by
    apply div_nonneg (Real.rpow_nonneg hx0.le _)
    have := Real.pi_pos
    positivity
  -- bound for the shifted kernel
  have hK : ‖(1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1‖
      ≤ x ^ (a - p.re) / (2 * π * Real.log x) * (4 / T) := by
    refine hJp.trans ?_
    apply mul_le_mul_of_nonneg_left _ hcab
    have e : -(-T - p.im) = T + p.im := by ring
    rw [e]
    have i1 : 1 / (T + p.im) ≤ 2 / T := by
      rw [div_le_div_iff₀ (by linarith) hT0]; linarith
    have i2 : 1 / (T - p.im) ≤ 2 / T := by
      rw [div_le_div_iff₀ (by linarith) hT0]; linarith
    have : (2 : ℝ) / T + 2 / T = 4 / T := by ring
    linarith
  have hK' : ‖(x : ℂ) ^ p *
      ((1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1)‖
      ≤ x ^ a / (2 * π * Real.log x) * (4 / T) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    calc x ^ p.re * ‖(1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1‖
        ≤ x ^ p.re * (x ^ (a - p.re) / (2 * π * Real.log x) * (4 / T)) :=
          mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hx0.le _)
      _ = x ^ a / (2 * π * Real.log x) * (4 / T) := by
          have : x ^ a = x ^ p.re * x ^ (a - p.re) := by
            rw [← Real.rpow_add hx0]; ring_nf
          rw [this]; ring
  have hJ0' : ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T, f₂ t) - 1‖
      ≤ x ^ a / (2 * π * Real.log x) * (2 / T) := by
    refine hJ0.trans ?_
    apply mul_le_mul_of_nonneg_left _ hc0
    rw [neg_neg]
    apply le_of_eq; ring
  have hp_norm : ‖(1 / p : ℂ)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr hp0)]
    have := Complex.abs_re_le_norm p
    have := le_abs_self p.re
    linarith
  -- combine
  have hsum : x ^ a / (2 * π * Real.log x) * (4 / T) + x ^ a / (2 * π * Real.log x) * (2 / T)
      ≤ 3 * x ^ a / T := by
    have hπl : 1 ≤ π * Real.log x := by nlinarith [Real.pi_gt_three]
    have : x ^ a / (2 * π * Real.log x) ≤ x ^ a / 2 := by
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (by norm_num)
      linarith
    have h4 : 0 ≤ 4 / T := by positivity
    have h2 : 0 ≤ 2 / T := by positivity
    calc x ^ a / (2 * π * Real.log x) * (4 / T) + x ^ a / (2 * π * Real.log x) * (2 / T)
        ≤ x ^ a / 2 * (4 / T) + x ^ a / 2 * (2 / T) := by
          gcongr
      _ = 3 * x ^ a / T := by ring
  calc ‖(1 / p) * ((x : ℂ) ^ p *
          ((1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1)
          - ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T, f₂ t) - 1)) - 1 / p‖
      ≤ ‖(1 / p) * ((x : ℂ) ^ p *
          ((1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1)
          - ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T, f₂ t) - 1))‖ + ‖(1 / p : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖(1 / p : ℂ)‖ * ‖(x : ℂ) ^ p *
          ((1 / (2 * π) : ℂ) * (∫ u in (-T - p.im)..(T - p.im), g u) - 1)
          - ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T, f₂ t) - 1)‖ + ‖(1 / p : ℂ)‖ := by
        rw [norm_mul]
    _ ≤ 2 * (x ^ a / (2 * π * Real.log x) * (4 / T) + x ^ a / (2 * π * Real.log x) * (2 / T))
          + 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add hK' hJ0')
    _ ≤ 2 * (3 * x ^ a / T) + 2 := by gcongr
    _ = 2 + 6 * x ^ a / T := by ring

/-! ## Case 2: `|Im p| > T/2` -/

private lemma d_case2 {p : ℂ} (hp1 : 1 / 2 ≤ p.re) (hp2 : p.re ≤ 1) {x a T : ℝ}
    (hx : 3 / 2 ≤ x) (ha : 1 < a) (hT : 2 ≤ T) (hγ : T / 2 < |p.im|) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p‖ ≤ 2 * x ^ a / T + x ^ a / (π * T) *
        ((2 + 2 * Real.log (3 * T / min (a - 1) 1)) + (2 + 2 * Real.log T)) := by
  have hp0 : p ≠ 0 := d_p_ne_zero hp1
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have ha0 : 0 < a := by linarith
  have hpa : p.re < a := by linarith
  have hT0 : 0 < T := by linarith
  have hpn : T / 2 < ‖p‖ := lt_of_lt_of_le hγ (Complex.abs_im_le_norm p)
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le a
  -- norm of the main term
  have hmain : ‖(x : ℂ) ^ p / p‖ ≤ 2 * x ^ a / T := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    calc x ^ p.re / ‖p‖ ≤ x ^ a / (T / 2) := by
          apply div_le_div₀ hxa (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
            (by linarith) hpn.le
      _ = 2 * x ^ a / T := by field_simp
  -- pointwise bound of the integrand
  have hpt : ∀ t : ℝ,
      ‖(x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p))‖
      ≤ x ^ a * (2 / T) * (1 / ‖(a : ℂ) + t * I - p‖ + 1 / ‖(a : ℂ) + t * I‖) := by
    intro t
    have h1 : 0 < ‖(a : ℂ) + t * I‖ := norm_pos_iff.mpr (d_s_ne_zero ha0 t)
    have h2 : 0 < ‖(a : ℂ) + t * I - p‖ := norm_pos_iff.mpr (d_sp_ne_zero hpa t)
    have htri : ‖p‖ ≤ ‖(a : ℂ) + t * I‖ + ‖(a : ℂ) + t * I - p‖ := by
      calc ‖p‖ = ‖((a : ℂ) + t * I) - ((a : ℂ) + t * I - p)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, d_re]
    rw [div_le_iff₀ (mul_pos h1 h2)]
    have e : (2 / T) * (1 / ‖(a : ℂ) + t * I - p‖ + 1 / ‖(a : ℂ) + t * I‖)
        * (‖(a : ℂ) + t * I‖ * ‖(a : ℂ) + t * I - p‖)
        = (2 / T) * (‖(a : ℂ) + t * I‖ + ‖(a : ℂ) + t * I - p‖) := by
      field_simp
    calc x ^ a = x ^ a * 1 := (mul_one _).symm
      _ ≤ x ^ a * ((2 / T) * (‖(a : ℂ) + t * I‖ + ‖(a : ℂ) + t * I - p‖)) := by
          apply mul_le_mul_of_nonneg_left _ hxa
          rw [div_mul_eq_mul_div, le_div_iff₀ hT0]; linarith
      _ = _ := by rw [← e]; ring
  -- integrate
  have hFc := d_cont_integrand hx0 ha0 hpa
  have hA := d_cont_one_div_norm_sp (a := a) hpa
  have hB := d_cont_one_div_norm_s (a := a) ha0
  have hGc : Continuous fun t : ℝ =>
      x ^ a * (2 / T) * (1 / ‖(a : ℂ) + t * I - p‖ + 1 / ‖(a : ℂ) + t * I‖) :=
    continuous_const.mul (hA.add hB)
  have hint : ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))‖
      ≤ 1 / (2 * π) * (x ^ a * (2 / T) *
        ((∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖) + ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I‖)) := by
    rw [norm_mul, d_norm_two_pi]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖∫ t in (-T)..T,
          (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p))‖
        ≤ ∫ t in (-T)..T,
          ‖(x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ t in (-T)..T,
          x ^ a * (2 / T) * (1 / ‖(a : ℂ) + t * I - p‖ + 1 / ‖(a : ℂ) + t * I‖) :=
          intervalIntegral.integral_mono_on (by linarith) (hFc.norm.intervalIntegrable _ _)
            (hGc.intervalIntegrable _ _) (fun t _ => hpt t)
      _ = x ^ a * (2 / T) *
          ((∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖) + ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I‖) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)]
  have hAb := d_A_bound ha hT hp2
  have hBb := d_B_bound ha.le (by linarith : 1 ≤ T)
  have hq : 0 ≤ x ^ a / (π * T) := by
    have := Real.pi_pos
    positivity
  calc ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p‖
      ≤ ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))‖
        + ‖(x : ℂ) ^ p / p‖ := norm_sub_le _ _
    _ ≤ 1 / (2 * π) * (x ^ a * (2 / T) *
        ((∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖) + ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I‖))
        + 2 * x ^ a / T := add_le_add hint hmain
    _ = x ^ a / (π * T) *
        ((∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I - p‖) + ∫ t in (-T)..T, 1 / ‖(a : ℂ) + t * I‖)
        + 2 * x ^ a / T := by
        ring
    _ ≤ x ^ a / (π * T) *
        ((2 + 2 * Real.log (3 * T / min (a - 1) 1)) + (2 + 2 * Real.log T)) + 2 * x ^ a / T := by
        gcongr
    _ = _ := by ring

/-! ## (D) The polar terms -/

private theorem polar_bound {p : ℂ} (hp1 : 1 / 2 ≤ p.re) (hp2 : p.re ≤ 1) {x a T : ℝ}
    (hx : 3 / 2 ≤ x) (ha : 1 < a) (ha3 : a ≤ 3) (hT : 2 ≤ T) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((a : ℂ) + t * I) / (((a : ℂ) + t * I) * ((a : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p‖
      ≤ 2 + 10 * x ^ a * (1 + Real.log T + Real.log (1 / (a - 1))) / T := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hlogT2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT : 1 / 2 ≤ Real.log T := le_trans d_log_two_ge hlogT2
  have hL : Real.log (1 / (a - 1)) = - Real.log (a - 1) := by rw [one_div, Real.log_inv]
  have hL1 : -Real.log 2 ≤ Real.log (1 / (a - 1)) := by
    rw [hL, neg_le_neg_iff]; exact Real.log_le_log (by linarith) (by linarith)
  have hq : 0 < x ^ a / T := by positivity
  rcases le_or_gt |p.im| (T / 2) with hγ | hγ
  · have h := d_case1 hp1 hp2 hx ha hT hγ
    refine h.trans ?_
    have h1 : 1 ≤ 1 + Real.log T + Real.log (1 / (a - 1)) := by linarith
    have : 6 * x ^ a / T ≤ 10 * x ^ a * (1 + Real.log T + Real.log (1 / (a - 1))) / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      nlinarith
    linarith
  · have h := d_case2 hp1 hp2 hx ha hT hγ
    refine h.trans ?_
    set δ := min (a - 1) 1 with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    have hlog3T : Real.log (3 * T / δ) = Real.log 3 + Real.log T - Real.log δ := by
      rw [Real.log_div (by positivity) hδ0.ne', Real.log_mul (by norm_num) hT0.ne']
    set S := (2 + 2 * Real.log (3 * T / δ)) + (2 + 2 * Real.log T) with hS
    have hS0 : 0 ≤ S := by
      have : 0 ≤ Real.log (3 * T / δ) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith [min_le_right (a - 1) 1])
      rw [hS]; linarith
    have h1 : x ^ a / (π * T) * S ≤ x ^ a / T * (S / 3) := by
      have : x ^ a / (π * T) ≤ x ^ a / T / 3 := by
        rw [div_div]
        exact div_le_div_of_nonneg_left hxa.le (by positivity)
          (by nlinarith [Real.pi_gt_three])
      calc x ^ a / (π * T) * S ≤ x ^ a / T / 3 * S := mul_le_mul_of_nonneg_right this hS0
        _ = x ^ a / T * (S / 3) := by ring
    have hscalar : 2 + S / 3 ≤ 10 * (1 + Real.log T + Real.log (1 / (a - 1))) := by
      have h3 := d_log_three_le
      have h2 := d_log_two_le
      rcases le_or_gt a 2 with ha2 | ha2
      · have hδa : δ = a - 1 := min_eq_left (by linarith)
        have hlogδ : Real.log δ ≤ 0 := by
          rw [hδa]; exact Real.log_nonpos (by linarith) (by linarith)
        rw [hS, hlog3T, hδa] at *
        rw [hL]
        linarith
      · have hδ1 : δ = 1 := min_eq_right (by linarith)
        rw [hS, hlog3T, hδ1, Real.log_one]
        linarith
    calc 2 * x ^ a / T + x ^ a / (π * T) * S ≤ 2 * x ^ a / T + x ^ a / T * (S / 3) := by
          linarith
      _ = x ^ a / T * (2 + S / 3) := by ring
      _ ≤ x ^ a / T * (10 * (1 + Real.log T + Real.log (1 / (a - 1)))) :=
          mul_le_mul_of_nonneg_left hscalar hq.le
      _ = 10 * x ^ a * (1 + Real.log T + Real.log (1 / (a - 1))) / T := by ring
      _ ≤ 2 + 10 * x ^ a * (1 + Real.log T + Real.log (1 / (a - 1))) / T := by linarith

/-! ## (D') Replacing `x = N - 1/2` by `N` -/

private theorem cpow_sub_cpow_div_le {p : ℂ} (hp1 : 1 / 2 ≤ p.re) (hp2 : p.re ≤ 1) {N : ℕ} (hN : 2 ≤ N)
    {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ‖(N : ℂ) ^ p / p - (x : ℂ) ^ p / p‖ ≤ 1 / 2 := by
  have hp0 : p ≠ 0 := d_p_ne_zero hp1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hxN : x ≤ N := by rw [hx]; linarith
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ p / p with hf
  have hderiv : ∀ t ∈ Icc x (N : ℝ), HasDerivWithinAt f ((t : ℂ) ^ (p - 1)) (Icc x (N : ℝ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by have := ht.1; intro h; linarith
    have hr : p - 1 ≠ -1 := by
      intro h; apply hp0; linear_combination h
    have := hasDerivAt_ofReal_cpow_const' ht0 hr
    simp only [sub_add_cancel] at this
    exact this.hasDerivWithinAt
  have hbound : ∀ t ∈ Ico x (N : ℝ), ‖(t : ℂ) ^ (p - 1)‖ ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (N : ℝ) ⟨hxN, le_refl _⟩
  simp only [hf] at key
  rw [Complex.ofReal_natCast] at key
  calc ‖(N : ℂ) ^ p / p - (x : ℂ) ^ p / p‖ ≤ 1 * ((N : ℝ) - x) := key
    _ = 1 / 2 := by rw [hx]; ring


/-! ### Piece `Assembly` -/

/-! ### Elementary real-number facts -/

private lemma f_exp_069_lt : Real.exp 0.69 < 2 := by
  have := Real.exp_bound' (x := 0.69) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

private lemma f_exp_one_lt : Real.exp 1 < 2.72 := by
  have := Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

private lemma f_two_lt_exp : 2 < Real.exp 0.7 := by
  have := Real.sum_le_exp_of_nonneg (x := 0.7) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

private lemma f_log_two_gt : 0.69 < Real.log 2 := by
  have h := f_exp_069_lt
  have := Real.log_lt_log (Real.exp_pos _) h
  rwa [Real.log_exp] at this

private lemma f_log_two_lt : Real.log 2 < 0.7 := by
  have h := f_two_lt_exp
  have := Real.log_lt_log (by norm_num) h
  rwa [Real.log_exp] at this

private lemma f_log_N_gt {N : ℕ} (hN : 2 ≤ N) : 0.69 < Real.log N := by
  have h2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have h3 := f_log_two_gt
  have h4 := Real.log_le_log (by norm_num) h2
  linarith

private lemma f_sqrt_ge {L : ℝ} (hL : 0.69 < L) : 0.8 ≤ Real.sqrt L := by
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  linarith

private lemma f_log_four_lt : Real.log 4 < 1.4 := by
  have : (4:ℝ) = 2 ^ 2 := by norm_num
  rw [this, Real.log_pow]
  have := f_log_two_lt
  push_cast
  linarith

private lemma f_exp_ge_two {u : ℝ} (hu8 : 0.8 ≤ u) : 2 ≤ Real.exp u := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u by linarith)
  have h2 : 0.8 * 0.8 ≤ u * u := mul_le_mul hu8 hu8 (by norm_num) (by linarith)
  linarith

private lemma f_ell_bounds {q : ℕ} (hq1 : 1 ≤ (q:ℝ)) {u : ℝ} (hu : 0.8 ≤ u) (hq : (q:ℝ) ≤ Real.exp u) :
    u ≤ Real.log ((q:ℝ) * (Real.exp u + 3)) ∧ Real.log ((q:ℝ) * (Real.exp u + 3)) ≤ 4 * u := by
  have hT : 0 < Real.exp u := Real.exp_pos u
  rw [Real.log_mul (by positivity) (by positivity)]
  constructor
  · have h1 : 0 ≤ Real.log q := Real.log_nonneg hq1
    have h2 : u ≤ Real.log (Real.exp u + 3) := by
      calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
        _ ≤ Real.log (Real.exp u + 3) := Real.log_le_log hT (by linarith)
    linarith
  · have h1 : Real.log q ≤ u := by
      have := Real.log_le_log (by linarith) hq
      rwa [Real.log_exp] at this
    have h2 : Real.log (Real.exp u + 3) ≤ Real.log 4 + u := by
      have h3 : Real.exp u + 3 ≤ 4 * Real.exp u := by linarith [f_exp_ge_two hu]
      calc Real.log (Real.exp u + 3) ≤ Real.log (4 * Real.exp u) :=
            Real.log_le_log (by positivity) h3
        _ = Real.log 4 + u := by rw [Real.log_mul (by norm_num) hT.ne', Real.log_exp]
    have h4 := f_log_four_lt
    linarith

/-- `N ^ σ = N * exp ((σ - 1) * log N)`. -/
private lemma f_rpow_N {N : ℕ} (hN : 2 ≤ N) (σ : ℝ) :
    (N:ℝ) ^ σ = (N:ℝ) * Real.exp ((σ - 1) * Real.log N) := by
  have hNpos : (0:ℝ) < N := by
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Real.rpow_def_of_pos hNpos]
  calc Real.exp (Real.log N * σ)
      = Real.exp (Real.log N) * Real.exp ((σ - 1) * Real.log N) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = N * Real.exp ((σ - 1) * Real.log N) := by rw [Real.exp_log hNpos]

private lemma f_line_re (σ t : ℝ) : ((σ:ℂ) + t * I).re = σ := by simp
private lemma f_line_im (σ t : ℝ) : ((σ:ℂ) + t * I).im = t := by simp

/-! ### The integral identity on the line -/

private lemma f_integral_identity (a : ℕ → ℂ) (H' : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ) (σ₀ x T : ℝ)
    (hT : 0 ≤ T) (hx : 0 < x) (hσ₀ : 0 < σ₀)
    (hP : ∀ p ∈ P, p.re < σ₀)
    (hcont : ContinuousOn (fun t : ℝ => H' ((σ₀:ℂ) + t * I)) (Icc (-T) T))
    (heq : ∀ t ∈ Icc (-T) T, LSeries a ((σ₀:ℂ) + t * I)
      = H' ((σ₀:ℂ) + t * I) + ∑ p ∈ P, r p / (((σ₀:ℂ) + t * I) - p)) :
    ∫ t in (-T)..T, LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)
    = (∫ t in (-T)..T, H' ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      + ∑ p ∈ P, r p * ∫ t in (-T)..T,
          (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - p)) := by
  have hs : Continuous (fun t : ℝ => (σ₀:ℂ) + t * I) := by fun_prop
  have hpow : Continuous (fun t : ℝ => (x:ℂ) ^ ((σ₀:ℂ) + t * I)) :=
    hs.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hne : ∀ t : ℝ, (σ₀:ℂ) + t * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnep : ∀ p ∈ P, ∀ t : ℝ, (σ₀:ℂ) + t * I - p ≠ 0 := by
    intro p hp t h
    have := congrArg Complex.re h
    simp at this
    linarith [hP p hp]
  have hI1 : IntervalIntegrable
      (fun t : ℝ => H' ((σ₀:ℂ) + t * I) * (x:ℂ) ^ ((σ₀:ℂ) + t * I) / ((σ₀:ℂ) + t * I))
      volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact (hcont.mul hpow.continuousOn).div hs.continuousOn (fun t _ => hne t)
  have hI2 : ∀ p ∈ P, Continuous
      (fun t : ℝ => r p * ((x:ℂ) ^ ((σ₀:ℂ) + t * I) / (((σ₀:ℂ) + t * I) * ((σ₀:ℂ) + t * I - p)))) := by
    intro p hp
    exact continuous_const.mul (hpow.div (hs.mul (hs.sub continuous_const))
      (fun t => mul_ne_zero (hne t) (hnep p hp t)))
  have hI3 : IntervalIntegrable
      (fun t : ℝ => ∑ p ∈ P, r p * ((x:ℂ) ^ ((σ₀:ℂ) + t * I) /
        (((σ₀:ℂ) + t * I) * ((σ₀:ℂ) + t * I - p)))) volume (-T) T :=
    (continuous_finsetSum P hI2).intervalIntegrable _ _
  have hEq : EqOn
      (fun t : ℝ => LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      (fun t : ℝ => H' ((σ₀:ℂ) + t * I) * (x:ℂ) ^ ((σ₀:ℂ) + t * I) / ((σ₀:ℂ) + t * I)
        + ∑ p ∈ P, r p * ((x:ℂ) ^ ((σ₀:ℂ) + t * I) / (((σ₀:ℂ) + t * I) * ((σ₀:ℂ) + t * I - p))))
      (uIcc (-T) T) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [heq t ht, add_mul, add_div, Finset.sum_mul, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [div_mul_eq_mul_div, div_div, mul_div_assoc, mul_comm ((σ₀:ℂ) + t * I - p)]
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_add hI1 hI3,
    intervalIntegral.integral_finsetSum (fun p hp => (hI2 p hp).intervalIntegrable _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [intervalIntegral.integral_const_mul]

/-! ### Algebraic decomposition -/

private lemma f_decomp (Sa IL IH k : ℂ) (P : Finset ℂ) (r Ip xp Np : ℂ → ℂ)
    (hIL : IL = IH + ∑ p ∈ P, r p * Ip p) :
    Sa - ∑ p ∈ P, r p * Np p
      = -(k * IL - Sa) + k * IH + ∑ p ∈ P, r p * (k * Ip p - xp p)
        + ∑ p ∈ P, r p * (xp p - Np p) := by
  have e1 : ∑ p ∈ P, r p * (k * Ip p - xp p)
      = k * ∑ p ∈ P, r p * Ip p - ∑ p ∈ P, r p * xp p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have e2 : ∑ p ∈ P, r p * (xp p - Np p) = ∑ p ∈ P, r p * xp p - ∑ p ∈ P, r p * Np p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [e1, e2, hIL]
  ring

/-! ### The extension `H'` on the rectangle -/

private lemma f_extension (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 < C₀)
    (q : ℕ) (hq1 : (1:ℝ) ≤ q) (G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hGan : AnalyticOnNhd ℂ G ({s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} \ ↑P))
    (hbd : ∀ s : ℂ, InRegion c q s → 3 / 4 ≤ s.re → s ∉ P →
        ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ C₀ * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (T ℓ c' σ₁ σ₀ : ℝ) (hℓ : ℓ = Real.log ((q:ℝ) * (T + 3))) (hℓpos : 0 < ℓ)
    (hc'c : c' < c) (hσ₁ : σ₁ = 1 - c' / ℓ) (hσ₁78 : 7 / 8 ≤ σ₁) :
    ∃ H' : ℂ → ℂ, DifferentiableOn ℂ H' (Icc σ₁ σ₀ ×ℂ Icc (-T) T) ∧
      (∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H' z‖ ≤ C₀ * ℓ ^ 2) ∧
      (∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, z ∉ P → H' z = G z - ∑ p ∈ P, r p / (z - p)) := by
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {s : ℂ | 1 - c / Real.log ((q:ℝ) * (|s.im| + 2)) < s.re ∧
      3 / 4 < s.re ∧ |s.im| < T + 1} := ⟨_, rfl⟩
  have hlogpos : ∀ s : ℂ, 0 < Real.log ((q:ℝ) * (|s.im| + 2)) := by
    intro s
    apply Real.log_pos
    have := mul_le_mul_of_nonneg_right hq1 (by positivity : (0:ℝ) ≤ |s.im| + 2)
    linarith [abs_nonneg s.im]
  have hUopen : IsOpen U := by
    have hcontlog : Continuous (fun s : ℂ => Real.log ((q:ℝ) * (|s.im| + 2))) := by
      apply Continuous.log
      · fun_prop
      · intro s; exact (mul_pos (by linarith) (by positivity)).ne'
    have hcont1 : Continuous (fun s : ℂ => 1 - c / Real.log ((q:ℝ) * (|s.im| + 2))) :=
      continuous_const.sub (continuous_const.div hcontlog (fun s => (hlogpos s).ne'))
    rw [hU, Set.setOf_and, Set.setOf_and]
    exact (isOpen_lt hcont1 Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hUsub : U ⊆ {s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} := by
    intro s hs
    rw [hU] at hs
    obtain ⟨h1, h2, _⟩ := hs
    exact ⟨h1.le, h2.le⟩
  have hlogle : ∀ z : ℂ, |z.im| < T + 1 → Real.log ((q:ℝ) * (|z.im| + 2)) ≤ ℓ := by
    intro z hz
    rw [hℓ]
    apply Real.log_le_log (mul_pos (by linarith) (by positivity))
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hHdiff : DifferentiableOn ℂ (fun s => G s - ∑ p ∈ P, r p / (s - p)) (U \ ↑P) := by
    apply DifferentiableOn.sub
    · exact hGan.differentiableOn.mono (Set.diff_subset_diff_left hUsub)
    · apply DifferentiableOn.fun_sum
      intro p hp
      apply DifferentiableOn.div (differentiableOn_const _)
        (differentiableOn_id.sub (differentiableOn_const _))
      intro z hz
      exact sub_ne_zero.mpr (fun h => hz.2 (Finset.mem_coe.mpr (h ▸ hp)))
  have hHB : ∀ z ∈ U \ ↑P, ‖G z - ∑ p ∈ P, r p / (z - p)‖ ≤ C₀ * ℓ ^ 2 := by
    intro z hz
    have hzU := hz.1
    have hzP : z ∉ P := fun h => hz.2 (Finset.mem_coe.mpr h)
    rw [hU] at hzU
    obtain ⟨h1, h2, h3⟩ := hzU
    refine (hbd z h1.le h2.le hzP).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact pow_le_pow_left₀ (hlogpos z).le (hlogle z h3) 2
  obtain ⟨H', hH'diff, hH'eq, hH'B⟩ := exists_extension_of_finite hUopen P hHdiff hHB
  have hRU : Icc σ₁ σ₀ ×ℂ Icc (-T) T ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨⟨hre1, hre2⟩, him1, him2⟩ := hz
    have habs : |z.im| ≤ T := abs_le.mpr ⟨him1, him2⟩
    rw [hU]
    refine ⟨?_, by linarith, by linarith⟩
    have h1 := hlogle z (by linarith)
    have h2 := hlogpos z
    have h3 : c / ℓ ≤ c / Real.log ((q:ℝ) * (|z.im| + 2)) :=
      div_le_div_of_nonneg_left hc.le h2 h1
    have h4 : c' / ℓ < c / ℓ := div_lt_div_of_pos_right hc'c hℓpos
    linarith
  refine ⟨H', hH'diff.mono hRU, fun z hz => hH'B z (hRU hz), fun z hz hzP => ?_⟩
  exact hH'eq z ⟨hRU hz, fun h => hzP (Finset.mem_coe.mp h)⟩

/-! ### Bound (C): the Perron error -/

private lemma f_bound_C {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) {L σ₀ T u E : ℝ}
    (hL : L = Real.log N) (hLpos : 0 < L) (hσ₀ : σ₀ = 1 + 1 / L) (hσ₀1 : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3)
    (hTpos : 0 < T) (hTinv : 1 / T = Real.exp (-u)) (hexpE : Real.exp (-u) ≤ E) (hE0 : 0 ≤ E)
    (hxσ₀ : x ^ σ₀ ≤ N * Real.exp 1) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      - ∑ n ∈ Finset.range N, a n‖ ≤ 110 * (N * (1 + L) ^ 2 * E) := by
  have hNpos : (0:ℝ) < N := by
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1 := perron_truncated ha hN hx hσ₀1 hTpos
  have h2 := perron_error_sum_le hN hx hσ₀1 hσ₀3
  have h3 := tsum_vonMangoldt_div_rpow_le hσ₀1 hσ₀3
  rw [← hL] at h2
  have h4 : 8 / (σ₀ - 1) ^ 2 = 8 * L ^ 2 := by
    rw [hσ₀]
    field_simp
    ring
  rw [h4] at h3
  have hS'0 : 0 ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ :=
    tsum_nonneg (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hxσ0 : 0 ≤ x ^ σ₀ := by
    have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have : 0 < x := by rw [hx]; linarith
    positivity
  have hexp1 := f_exp_one_lt
  have hY0 : 0 ≤ (N:ℝ) * (1 + L) ^ 2 := by positivity
  have h6 : ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ 318 * (N * (1 + L) ^ 2) := by
    refine h2.trans ?_
    have h7 : 10 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
        ≤ 10 * (N * Real.exp 1) * (8 * L ^ 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hxσ₀ (by norm_num)) h3 hS'0 (by positivity)
    have h8 : (N:ℝ) * Real.exp 1 * L ^ 2 ≤ N * 2.72 * L ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1.le hNpos.le) (sq_nonneg L)
    have h9 : (N:ℝ) * L ^ 2 ≤ N * (1 + L) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLpos.le (by linarith) 2) hNpos.le
    linarith
  have hpi : 1 / π ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_three.le
  have hYE : (N:ℝ) * (1 + L) ^ 2 * Real.exp (-u) ≤ N * (1 + L) ^ 2 * E :=
    mul_le_mul_of_nonneg_left hexpE hY0
  calc _ ≤ 1 / (π * T) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
          |Real.log (x / n)| := h1
    _ ≤ 1 / (π * T) * (318 * (N * (1 + L) ^ 2)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = 318 * (1 / π) * (N * (1 + L) ^ 2 * (1 / T)) := by ring
    _ = 318 * (1 / π) * (N * (1 + L) ^ 2 * Real.exp (-u)) := by rw [hTinv]
    _ ≤ 106 * (N * (1 + L) ^ 2 * E) := by
        apply mul_le_mul (by linarith) hYE (by positivity) (by norm_num)
    _ ≤ 110 * (N * (1 + L) ^ 2 * E) := by
        have : 0 ≤ (N:ℝ) * (1 + L) ^ 2 * E := by positivity
        linarith

/-! ### Bound (E): the shifted integral -/

private lemma f_bound_E {H' : ℂ → ℂ} {C₀ N σ₁ σ₀ T x B L u E : ℝ} (hC₀ : 0 < C₀)
    (hNpos : 0 < N) (hσ₁78 : 7 / 8 ≤ σ₁) (hσ₁1 : σ₁ < 1) (hσ₁σ₀ : σ₁ ≤ σ₀) (hσdiff : σ₀ - σ₁ ≤ 2)
    (hT2 : 2 ≤ T) (hx1 : 1 ≤ x) (hB0 : 0 ≤ B) (hB16 : B ≤ 16 * C₀ * L) (hLpos : 0 < L)
    (hH : DifferentiableOn ℂ H' (Icc σ₁ σ₀ ×ℂ Icc (-T) T))
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H' z‖ ≤ B)
    (hxσ₁ : x ^ σ₁ ≤ N * E) (hxσ₀T : x ^ σ₀ / T ≤ N * Real.exp 1 * E)
    (hlogT : Real.log T = u) (huL' : u ≤ 1 + L) (hE0 : 0 ≤ E) :
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        H' ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖
      ≤ 60 * C₀ * (N * (1 + L) ^ 2 * E) := by
  have hTpos : 0 < T := by linarith
  have h1 := shift_bound (H := H') (by linarith : 0 < σ₁) hσ₁1.le hσ₁σ₀ (by linarith : 1 ≤ T)
    hx1 hB0 hH hHB
  have hexp1 := f_exp_one_lt
  have hlogTσ : Real.log (T / σ₁) ≤ 1 + u := by
    have h1 : T / σ₁ ≤ 2 * T := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hσ₁78 hTpos.le
      linarith
    have h2 : 0 < T / σ₁ := div_pos hTpos (by linarith)
    calc Real.log (T / σ₁) ≤ Real.log (2 * T) := Real.log_le_log h2 h1
      _ = Real.log 2 + u := by rw [Real.log_mul (by norm_num) hTpos.ne', hlogT]
      _ ≤ 1 + u := by linarith [f_log_two_lt]
  have hlogT0 : 0 ≤ Real.log (T / σ₁) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hxσ₁0 : 0 ≤ x ^ σ₁ := by positivity
  have hterm1 : x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) ≤ N * E * (8 * (1 + L)) := by
    apply mul_le_mul hxσ₁ _ (by linarith) (by positivity)
    linarith
  have hterm2 : 2 * (σ₀ - σ₁) * x ^ σ₀ / T ≤ 4 * (N * Real.exp 1 * E) := by
    rw [mul_div_assoc]
    calc 2 * (σ₀ - σ₁) * (x ^ σ₀ / T) ≤ 2 * 2 * (N * Real.exp 1 * E) :=
          mul_le_mul (by linarith) hxσ₀T (by positivity) (by norm_num)
      _ = 4 * (N * Real.exp 1 * E) := by ring
  have hNE : 0 ≤ N * E := by positivity
  have hinside : x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + 2 * (σ₀ - σ₁) * x ^ σ₀ / T
      ≤ 19 * (1 + L) * (N * E) := by
    have : 4 * (N * Real.exp 1 * E) ≤ 11 * (1 + L) * (N * E) := by
      have h1 := mul_le_mul_of_nonneg_left hexp1.le hNE
      have h2 := mul_nonneg hNE hLpos.le
      linarith
    linarith
  have hinside0 : 0 ≤ x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + 2 * (σ₀ - σ₁) * x ^ σ₀ / T := by
    apply add_nonneg (mul_nonneg hxσ₁0 (by linarith))
    apply div_nonneg _ hTpos.le
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have hBpi : B / (2 * π) ≤ 3 * C₀ * (1 + L) := by
    rw [div_le_iff₀ (by positivity)]
    have hpi := Real.pi_gt_three
    have h1 := mul_nonneg hC₀.le hLpos.le
    have h2 := mul_nonneg (mul_nonneg hC₀.le (by linarith : (0:ℝ) ≤ 1 + L))
      (by linarith : (0:ℝ) ≤ π - 3)
    linarith
  calc _ ≤ B / (2 * π) * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁))
        + 2 * (σ₀ - σ₁) * x ^ σ₀ / T) := h1
    _ ≤ 3 * C₀ * (1 + L) * (19 * (1 + L) * (N * E)) :=
        mul_le_mul hBpi hinside hinside0 (by positivity)
    _ = 57 * C₀ * (N * (1 + L) ^ 2 * E) := by ring
    _ ≤ 60 * C₀ * (N * (1 + L) ^ 2 * E) := by
        have : 0 ≤ C₀ * (N * (1 + L) ^ 2 * E) := by positivity
        linarith

/-! ### Bound (D): the polar terms (uniform in the pole) -/

private lemma f_bound_D {p : ℂ} (hp1 : 1 / 2 ≤ p.re) (hp2 : p.re ≤ 1) {x σ₀ T L u N E : ℝ}
    (hx32 : 3 / 2 ≤ x) (hσ₀ : σ₀ = 1 + 1 / L) (hσ₀1 : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3) (hT2 : 2 ≤ T)
    (hLpos : 0 < L) (hlogT : Real.log T = u) (huL' : u ≤ 1 + L)
    (hxσ₀T : x ^ σ₀ / T ≤ N * Real.exp 1 * E) (hNpos : 0 < N) (hE0 : 0 ≤ E) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - p)))
      - (x : ℂ) ^ p / p‖ ≤ 2 + 55 * (N * (1 + L) * E) := by
  have hTpos : 0 < T := by linarith
  have h1 := polar_bound hp1 hp2 hx32 hσ₀1 hσ₀3 hT2
  refine h1.trans ?_
  have hexp1 := f_exp_one_lt
  have hlogL : Real.log (1 / (σ₀ - 1)) ≤ L := by
    rw [hσ₀]
    have : 1 + 1 / L - 1 = 1 / L := by ring
    rw [this, one_div_one_div]
    linarith [Real.log_le_sub_one_of_pos hLpos]
  have hfac : 1 + Real.log T + Real.log (1 / (σ₀ - 1)) ≤ 2 * (1 + L) := by
    rw [hlogT]; linarith
  have hxσ₀0 : 0 ≤ x ^ σ₀ / T := by positivity
  have h2 : 10 * x ^ σ₀ * (1 + Real.log T + Real.log (1 / (σ₀ - 1))) / T
      ≤ 10 * (N * Real.exp 1 * E) * (2 * (1 + L)) := by
    calc 10 * x ^ σ₀ * (1 + Real.log T + Real.log (1 / (σ₀ - 1))) / T
        = 10 * (x ^ σ₀ / T) * (1 + Real.log T + Real.log (1 / (σ₀ - 1))) := by ring
      _ ≤ 10 * (x ^ σ₀ / T) * (2 * (1 + L)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ ≤ 10 * (N * Real.exp 1 * E) * (2 * (1 + L)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxσ₀T (by norm_num))
            (by positivity)
  have h3 : 10 * (N * Real.exp 1 * E) * (2 * (1 + L)) ≤ 55 * (N * (1 + L) * E) := by
    have h0 : 0 ≤ N * (1 + L) * E := by positivity
    have h1 := mul_le_mul_of_nonneg_left hexp1.le h0
    linarith
  linarith

/-! ### The main bound with explicit constants -/

private theorem f_main_bound (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 < C₀)
    (q : ℕ) [NeZero q] (a : ℕ → ℂ) (G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    (hGan : AnalyticOnNhd ℂ G ({s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} \ ↑P))
    (hP : ∀ p ∈ P, 1 / 2 ≤ p.re ∧ p.re ≤ 1)
    (hr : (∑ p ∈ P, ‖r p‖) ≤ C₀ * Real.log (2 * q))
    (hbd : ∀ s : ℂ, InRegion c q s → 3 / 4 ≤ s.re → s ∉ P →
        ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ C₀ * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (N : ℕ) (hN : 2 ≤ N) (hq : (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) :
    ‖(∑ n ∈ range N, a n) - ∑ p ∈ P, r p * (N : ℂ) ^ p / p‖
      ≤ (110 + 385 * C₀) * N * (1 + Real.log N) ^ 2 *
          Real.exp (-(min (c / 2) (1 / 10) / 4) * Real.sqrt (Real.log N)) := by
  /- ### Parameters -/
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log N := ⟨_, rfl⟩
  have hL69 : 0.69 < L := hL ▸ f_log_N_gt hN
  have hLpos : 0 < L := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt L := ⟨_, rfl⟩
  have hu8 : 0.8 ≤ u := hu ▸ f_sqrt_ge hL69
  have hu0 : 0 ≤ u := by linarith
  have huL : u * u = L := by rw [hu, Real.mul_self_sqrt hLpos.le]
  have huL' : u ≤ 1 + L := by
    have h1 : u * u - 2 * u + 1 = (u - 1) * (u - 1) := by ring
    have h2 := mul_self_nonneg (u - 1)
    linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp u := ⟨_, rfl⟩
  have hT2 : 2 ≤ T := hT ▸ f_exp_ge_two hu8
  have hTpos : 0 < T := by linarith
  have hlogT : Real.log T = u := by rw [hT, Real.log_exp]
  have hTinv : 1 / T = Real.exp (-u) := by rw [hT, Real.exp_neg, one_div]
  rw [← hL, ← hu, ← hT] at hq
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q:ℝ) * (T + 3)) := ⟨_, rfl⟩
  have hℓu : u ≤ ℓ ∧ ℓ ≤ 4 * u := by
    have := f_ell_bounds hq1 hu8 (hT ▸ hq)
    rwa [← hT, ← hℓ] at this
  have hℓpos : 0 < ℓ := by linarith
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = min (c / 2) (1 / 10) := ⟨_, rfl⟩
  have hc'pos : 0 < c' := by rw [hc']; exact lt_min (by linarith) (by norm_num)
  have hc'10 : c' ≤ 1 / 10 := by rw [hc']; exact min_le_right _ _
  have hc'c : c' < c := by rw [hc']; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = c' / 4 := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκ1 : κ ≤ 1 := by rw [hκ]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-κ * u) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; positivity
  have hexpE : Real.exp (-u) ≤ E := by
    rw [hE]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (sub_nonneg.2 hκ1) hu0
    linarith
  rw [← hL, ← hu, ← hc', ← hκ, ← hE]
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / L := ⟨_, rfl⟩
  have hLinv : 1 / L ≤ 1.45 := by rw [div_le_iff₀ hLpos]; linarith
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; have := one_div_pos.mpr hLpos; linarith
  have hσ₀3 : σ₀ ≤ 3 := by rw [hσ₀]; linarith
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = 1 - c' / ℓ := ⟨_, rfl⟩
  have hc'ℓ : c' / ℓ ≤ 1 / 8 := by rw [div_le_iff₀ hℓpos]; linarith
  have hσ₁78 : 7 / 8 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁]; have := div_pos hc'pos hℓpos; linarith
  have hσ₁σ₀ : σ₁ ≤ σ₀ := by linarith
  have hσdiff : σ₀ - σ₁ ≤ 2 := by rw [hσ₀, hσ₁]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N:ℝ) - 1 / 2 := ⟨_, rfl⟩
  have hx32 : 3 / 2 ≤ x := by rw [hx]; linarith
  have hxpos : 0 < x := by linarith
  have hxN : x ≤ N := by rw [hx]; linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C₀ * ℓ ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hB16 : B ≤ 16 * C₀ * L := by
    have h1 : ℓ ^ 2 ≤ (4 * u) ^ 2 := pow_le_pow_left₀ hℓpos.le hℓu.2 2
    calc B = C₀ * ℓ ^ 2 := hB
      _ ≤ C₀ * (4 * u) ^ 2 := mul_le_mul_of_nonneg_left h1 hC₀.le
      _ = 16 * C₀ * L := by rw [← huL]; ring
  have hxσ₀ : x ^ σ₀ ≤ N * Real.exp 1 := by
    calc x ^ σ₀ ≤ (N:ℝ) ^ σ₀ := Real.rpow_le_rpow hxpos.le hxN (by linarith)
      _ = N * Real.exp 1 := by
        rw [f_rpow_N hN, ← hL, hσ₀]
        have : (1 + 1 / L - 1) * L = 1 := by field_simp; ring
        rw [this]
  have hxσ₀T : x ^ σ₀ / T ≤ N * Real.exp 1 * E := by
    rw [div_le_iff₀ hTpos]
    calc x ^ σ₀ ≤ N * Real.exp 1 := hxσ₀
      _ = N * Real.exp 1 * (Real.exp (-u) * T) := by rw [hT, ← Real.exp_add]; simp
      _ ≤ N * Real.exp 1 * (E * T) := by gcongr
      _ = N * Real.exp 1 * E * T := by ring
  have hxσ₁ : x ^ σ₁ ≤ N * E := by
    calc x ^ σ₁ ≤ (N:ℝ) ^ σ₁ := Real.rpow_le_rpow hxpos.le hxN (by linarith)
      _ = N * Real.exp ((σ₁ - 1) * L) := by rw [f_rpow_N hN, ← hL]
      _ ≤ N * E := by
        apply mul_le_mul_of_nonneg_left _ hNpos.le
        rw [hE]
        apply Real.exp_le_exp.mpr
        rw [hσ₁, hκ]
        have : c' / 4 * u ≤ c' / ℓ * L := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) hℓpos]
          rw [← huL]
          have := mul_nonneg (mul_nonneg hc'pos.le hu0) (sub_nonneg.2 hℓu.2)
          linarith
        linarith
  /- ### The extension `H'`, the rectangle and the line -/
  obtain ⟨H', hH'diff, hH'B, hH'eq⟩ := f_extension c C₀ hc hC₀ q hq1 G P r hGan hbd T ℓ c' σ₁ σ₀
    hℓ hℓpos hc'c hσ₁ hσ₁78
  rw [← hB] at hH'B
  have hline : ∀ t ∈ Icc (-T) T, (σ₀:ℂ) + t * I ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T := by
    intro t ht
    rw [Complex.mem_reProdIm, f_line_re, f_line_im]
    exact ⟨⟨hσ₁σ₀, le_rfl⟩, ht⟩
  have hlineP : ∀ t : ℝ, (σ₀:ℂ) + t * I ∉ P := by
    intro t h
    have := (hP _ h).2
    rw [f_line_re] at this
    linarith
  have hcont : ContinuousOn (fun t : ℝ => H' ((σ₀:ℂ) + t * I)) (Icc (-T) T) := by
    apply hH'diff.continuousOn.comp
      (by fun_prop : Continuous (fun t : ℝ => (σ₀:ℂ) + t * I)).continuousOn
    intro t ht
    exact hline t ht
  have heq : ∀ t ∈ Icc (-T) T, LSeries a ((σ₀:ℂ) + t * I)
      = H' ((σ₀:ℂ) + t * I) + ∑ p ∈ P, r p / (((σ₀:ℂ) + t * I) - p) := by
    intro t ht
    rw [hH'eq _ (hline t ht) (hlineP t), ← hG _ (by rw [f_line_re]; exact hσ₀1)]
    ring
  /- ### The integral identity and the decomposition -/
  obtain ⟨IL, hILdef⟩ : ∃ IL : ℂ, IL = ∫ t in (-T)..T, LSeries a ((σ₀ : ℂ) + t * I) *
      (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := ⟨_, rfl⟩
  obtain ⟨IH, hIHdef⟩ : ∃ IH : ℂ, IH = ∫ t in (-T)..T, H' ((σ₀ : ℂ) + t * I) *
      (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := ⟨_, rfl⟩
  obtain ⟨Ip, hIpdef⟩ : ∃ Ip : ℂ → ℂ, Ip = fun p => ∫ t in (-T)..T,
      (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - p)) := ⟨_, rfl⟩
  have hIL : IL = IH + ∑ p ∈ P, r p * Ip p := by
    rw [hILdef, hIHdef, hIpdef]
    exact f_integral_identity a H' P r σ₀ x T hTpos.le hxpos (by linarith)
      (fun p hp => by linarith [(hP p hp).2]) hcont heq
  have hsumN : ∑ p ∈ P, r p * (N:ℂ) ^ p / p = ∑ p ∈ P, r p * ((N:ℂ) ^ p / p) :=
    Finset.sum_congr rfl (fun p _ => mul_div_assoc _ _ _)
  rw [hsumN, f_decomp (∑ n ∈ range N, a n) IL IH (1 / (2 * π) : ℂ) P r Ip
    (fun p => (x:ℂ) ^ p / p) (fun p => (N:ℂ) ^ p / p) hIL]
  /- ### Bounds for the four pieces -/
  have hC : ‖(1 / (2 * π) : ℂ) * IL - ∑ n ∈ range N, a n‖ ≤ 110 * (N * (1 + L) ^ 2 * E) := by
    rw [hILdef]
    exact f_bound_C ha hN hx hL hLpos hσ₀ hσ₀1 hσ₀3 hTpos hTinv hexpE hEpos.le hxσ₀
  have hEb : ‖(1 / (2 * π) : ℂ) * IH‖ ≤ 60 * C₀ * (N * (1 + L) ^ 2 * E) := by
    rw [hIHdef]
    exact f_bound_E hC₀ hNpos hσ₁78 hσ₁1 hσ₁σ₀ hσdiff hT2 (by linarith) hB0 hB16 hLpos hH'diff
      hH'B hxσ₁ hxσ₀T hlogT huL' hEpos.le
  have hlog2q : Real.log (2 * q) ≤ 1 + u := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log q ≤ u := by
      have := Real.log_le_log (by linarith) hq
      rwa [hT, Real.log_exp] at this
    linarith [f_log_two_lt]
  have hrsum : ∑ p ∈ P, ‖r p‖ ≤ C₀ * (1 + u) :=
    hr.trans (mul_le_mul_of_nonneg_left hlog2q hC₀.le)
  have hD : ‖∑ p ∈ P, r p * ((1 / (2 * π) : ℂ) * Ip p - (x:ℂ) ^ p / p)‖
      ≤ 2 * C₀ * (1 + u) + 110 * C₀ * (N * (1 + L) ^ 2 * E) := by
    have hM : ∀ p ∈ P, ‖(1 / (2 * π) : ℂ) * Ip p - (x:ℂ) ^ p / p‖
        ≤ 2 + 55 * (N * (1 + L) * E) := by
      intro p hp
      rw [hIpdef]
      exact f_bound_D (hP p hp).1 (hP p hp).2 hx32 hσ₀ hσ₀1 hσ₀3 hT2 hLpos hlogT huL'
        hxσ₀T hNpos hEpos.le
    have hM0 : 0 ≤ 2 + 55 * ((N:ℝ) * (1 + L) * E) := by positivity
    calc _ ≤ ∑ p ∈ P, ‖r p‖ * (2 + 55 * (N * (1 + L) * E)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM p hp) (norm_nonneg _)
      _ = (∑ p ∈ P, ‖r p‖) * (2 + 55 * (N * (1 + L) * E)) := by rw [Finset.sum_mul]
      _ ≤ C₀ * (1 + u) * (2 + 55 * (N * (1 + L) * E)) :=
          mul_le_mul_of_nonneg_right hrsum hM0
      _ ≤ 2 * C₀ * (1 + u) + 110 * C₀ * (N * (1 + L) ^ 2 * E) := by
          have h1 : 1 + u ≤ 2 * (1 + L) := by linarith
          have h2 : 0 ≤ C₀ * (N * (1 + L) * E) := by positivity
          linarith [mul_le_mul_of_nonneg_left h1 h2]
  have hD' : ‖∑ p ∈ P, r p * ((x:ℂ) ^ p / p - (N:ℂ) ^ p / p)‖ ≤ C₀ * (1 + u) / 2 := by
    calc _ ≤ ∑ p ∈ P, ‖r p‖ * (1 / 2) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
          rw [norm_mul, norm_sub_rev]
          exact mul_le_mul_of_nonneg_left
            (cpow_sub_cpow_div_le (hP p hp).1 (hP p hp).2 hN hx) (norm_nonneg _)
      _ = (∑ p ∈ P, ‖r p‖) * (1 / 2) := by rw [Finset.sum_mul]
      _ ≤ C₀ * (1 + u) * (1 / 2) := mul_le_mul_of_nonneg_right hrsum (by norm_num)
      _ = C₀ * (1 + u) / 2 := by ring
  have hleft : C₀ * (1 + u) ≤ 2 * C₀ * (N * (1 + L) ^ 2 * E) := by
    have hNE : 1 ≤ (N:ℝ) * E := by
      have hNexp : (N:ℝ) = Real.exp L := by rw [hL, Real.exp_log hNpos]
      have hκu : κ * u ≤ L := by
        rw [hκ]
        have := mul_le_mul hc'10 huL' hu0 (by norm_num)
        linarith
      rw [hNexp, hE, ← Real.exp_add]
      linarith [Real.add_one_le_exp (L + -κ * u)]
    have h1 : 1 + u ≤ 2 * (1 + L) ^ 2 := by
      have := sq_nonneg L
      linarith
    calc C₀ * (1 + u) ≤ C₀ * (2 * (1 + L) ^ 2) := mul_le_mul_of_nonneg_left h1 hC₀.le
      _ ≤ C₀ * (2 * (1 + L) ^ 2) * (N * E) := le_mul_of_one_le_right (by positivity) hNE
      _ = 2 * C₀ * (N * (1 + L) ^ 2 * E) := by ring
  /- ### Adding up -/
  refine norm_add₄_le.trans ?_
  rw [norm_neg]
  have hCY0 : 0 ≤ C₀ * ((N:ℝ) * (1 + L) ^ 2 * E) := by positivity
  have hfinal : (110 + 385 * C₀) * (N:ℝ) * (1 + L) ^ 2 * E
      = 110 * (N * (1 + L) ^ 2 * E) + 385 * (C₀ * (N * (1 + L) ^ 2 * E)) := by ring
  rw [hfinal]
  linarith

/-! ### The platform theorem -/

private theorem main (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 < C₀) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (a : ℕ → ℂ) (G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) →
        (∀ s : ℂ, 1 < s.re → G s = LSeries a s) →
        AnalyticOnNhd ℂ G ({s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} \ ↑P) →
        (∀ p ∈ P, 1 / 2 ≤ p.re ∧ p.re ≤ 1) →
        (∑ p ∈ P, ‖r p‖) ≤ C₀ * Real.log (2 * q) →
        (∀ s : ℂ, InRegion c q s → 3 / 4 ≤ s.re → s ∉ P →
            ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ C₀ * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2) →
        ∀ N : ℕ, 2 ≤ N → (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) →
          ‖(∑ n ∈ range N, a n) - ∑ p ∈ P, r p * (N : ℂ) ^ p / p‖
            ≤ C * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) := by
  have hκ : 0 < min (c / 2) (1 / 10) / 4 := by
    have : 0 < min (c / 2) (1 / 10) := lt_min (by linarith) (by norm_num)
    positivity
  obtain ⟨CA, hCA, hA⟩ := absorb hκ
  refine ⟨min (c / 2) (1 / 10) / 4 / 2, 1, (110 + 385 * C₀) * CA, by positivity, by norm_num,
    by positivity, ?_⟩
  intro q _ a G P r ha hG hGan hP hr hbd N hN hq
  rw [one_mul] at hq
  have hmain := f_main_bound c C₀ hc hC₀ q a G P r ha hG hGan hP hr hbd N hN hq
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsq : (1 + Real.log N) ^ 2 = (1 + Real.sqrt (Real.log N) ^ 2) ^ 2 := by
    rw [Real.sq_sqrt hL0]
  have hA' := hA (Real.sqrt (Real.log N)) (Real.sqrt_nonneg _)
  have hN0 : (0:ℝ) ≤ N := by positivity
  have hK0 : (0:ℝ) ≤ 110 + 385 * C₀ := by positivity
  calc _ ≤ (110 + 385 * C₀) * N * (1 + Real.log N) ^ 2 *
          Real.exp (-(min (c / 2) (1 / 10) / 4) * Real.sqrt (Real.log N)) := hmain
    _ = (110 + 385 * C₀) * N * ((1 + Real.sqrt (Real.log N) ^ 2) ^ 2 *
          Real.exp (-(min (c / 2) (1 / 10) / 4) * Real.sqrt (Real.log N))) := by
        rw [hsq]; ring
    _ ≤ (110 + 385 * C₀) * N * (CA * Real.exp (-(min (c / 2) (1 / 10) / 4 / 2) *
          Real.sqrt (Real.log N))) := by gcongr
    _ = (110 + 385 * C₀) * CA * N * Real.exp (-(min (c / 2) (1 / 10) / 4 / 2) *
          Real.sqrt (Real.log N)) := by ring


end TP
end Davenport

open Davenport in
/-- Davenport §17–18: partial sums of a Dirichlet series with von Mangoldt-size coefficients
from a zero-free region, via the truncated Perron formula. -/
theorem _root_.SWPort.Davenport.perron_of_region_bound_oai (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 < C₀) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (a : ℕ → ℂ) (G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) →
        (∀ s : ℂ, 1 < s.re → G s = LSeries a s) →
        AnalyticOnNhd ℂ G ({s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} \ ↑P) →
        (∀ p ∈ P, 1 / 2 ≤ p.re ∧ p.re ≤ 1) →
        (∑ p ∈ P, ‖r p‖) ≤ C₀ * Real.log (2 * q) →
        (∀ s : ℂ, InRegion c q s → 3 / 4 ≤ s.re → s ∉ P →
            ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ C₀ * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2) →
        ∀ N : ℕ, 2 ≤ N → (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) →
          ‖(∑ n ∈ range N, a n) - ∑ p ∈ P, r p * (N : ℂ) ^ p / p‖
            ≤ C * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) :=
  Davenport.TP.main c C₀ hc hC₀

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.perron_of_region_bound_oai := @SWPort.Davenport.perron_of_region_bound_oai
