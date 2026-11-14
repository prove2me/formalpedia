-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.exists_facialReparam_of_exteriorParam
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:42:51.421181+00:00
-- url     : https://prove2.me/submissions/a64eb40a-a3ae-4751-b619-f089a85ca275

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry
import Definitions.Def_Schoenflies_Bounded
import Definitions.Def_Schoenflies_Graph_OuterFace
import Theorems.Thm_JordanCurve_jordan_curve_theorem
import Theorems.Thm_JordanCurve_euclidean_unit_circle_loop
import Theorems.Thm_JordanCurve_simple_arc_complement_connected
import Theorems.Thm_compact_singleton_attachment_region_preconnected

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
/-- The hypotheses of `exists_facialReparam_of_exteriorParam`, bundled. -/
structure Hyp {V : Type} [Fintype V] {G : SimpleGraph V} (D : PlaneDrawing G)
    (F : ℝ → ℝ → Plane) : Prop where
  connected : G.Connected
  nontrivial : ∃ v w : V, v ≠ w
  cont : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ)
  per : ∀ r t, F r (t + 1) = F r t
  inj : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1)
  onto : Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = D.outerFace Set.univ
  bdry : Set.range (F 0) = frontier (D.outerFace Set.univ)
  light : ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β, F 0 θ ≠ F 0 α

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
/-! ## Jordan curves in `ℝ × ℝ` (copied from `PartA` / `FWPartC`) -/
/-- A homeomorphism between the plane `ℝ × ℝ` and Euclidean space. -/
noncomputable def planeHomeo : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph

abbrev Circle2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

theorem circle_param {f : unitInterval → ℝ × ℝ} (hf : Continuous f)
    (hf01 : f 0 = f 1)
    (hinj : ∀ s t : unitInterval, f s = f t →
      s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0)) :
    ∃ g : Circle2 → ℝ × ℝ, Continuous g ∧ Function.Injective g ∧
      Set.range g = Set.range f := by
  obtain ⟨e, hec, he01, heinj, hesurj⟩ := JordanCurve.euclidean_unit_circle_loop
  have hpre : ∀ p : Circle2, ∃ u, u ∈ Set.Icc (0 : ℝ) 1 ∧ e u = p := by
    intro p
    have : p ∈ e '' Set.Icc 0 1 := by rw [hesurj]; trivial
    exact this
  choose U hU heU using hpre
  let g : Circle2 → ℝ × ℝ := fun p => f ⟨U p, hU p⟩
  have ecoll : ∀ u v : ℝ, (hu : u ∈ Set.Icc (0 : ℝ) 1) → (hv : v ∈ Set.Icc (0 : ℝ) 1) →
      e u = e v → f ⟨u, hu⟩ = f ⟨v, hv⟩ := by
    intro u v hu hv huv
    have h0 : f ⟨0, by simp⟩ = f ⟨1, by simp⟩ := hf01
    rcases lt_or_eq_of_le hu.2 with hu1 | hu1 <;> rcases lt_or_eq_of_le hv.2 with hv1 | hv1
    · have := heinj ⟨hu.1, hu1⟩ ⟨hv.1, hv1⟩ huv
      subst this; rfl
    · subst hv1
      have := heinj ⟨hu.1, hu1⟩ ⟨le_refl 0, zero_lt_one⟩ (huv.trans he01.symm)
      subst this; exact h0
    · subst hu1
      have := heinj ⟨hv.1, hv1⟩ ⟨le_refl 0, zero_lt_one⟩ (huv.symm.trans he01.symm)
      subst this; exact h0.symm
    · subst hu1; subst hv1; rfl
  have hge : ∀ u (hu : u ∈ Set.Icc (0 : ℝ) 1), g (e u) = f ⟨u, hu⟩ :=
    fun u hu => ecoll _ _ _ _ (heU (e u))
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [continuous_iff_isClosed]
    intro F hF
    have hK : IsCompact (Set.Icc (0 : ℝ) 1 ∩
        (fun u => f (Set.projIcc (0 : ℝ) 1 zero_le_one u)) ⁻¹' F) :=
      isCompact_Icc.inter_right (hF.preimage (hf.comp continuous_projIcc))
    have hpre : g ⁻¹' F = e '' (Set.Icc (0 : ℝ) 1 ∩
        (fun u => f (Set.projIcc (0 : ℝ) 1 zero_le_one u)) ⁻¹' F) := by
      ext p
      constructor
      · intro hp
        refine ⟨U p, ⟨hU p, ?_⟩, heU p⟩
        simp only [Set.mem_preimage, Set.projIcc_of_mem _ (hU p)]
        exact hp
      · rintro ⟨u, ⟨hu, hF'⟩, rfl⟩
        show g (e u) ∈ F
        rw [hge u hu]
        simpa only [Set.mem_preimage, Set.projIcc_of_mem _ hu] using hF'
    rw [hpre]
    exact (hK.image_of_continuousOn (hec.mono Set.inter_subset_left)).isClosed
  · intro p q hpq
    rcases hinj _ _ hpq with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← heU p, ← heU q]
      exact congrArg e (congrArg Subtype.val h)
    · change U p = 0 at h1
      change U q = 1 at h2
      rw [← heU p, ← heU q, h1, h2, he01]
    · change U p = 1 at h1
      change U q = 0 at h2
      rw [← heU p, ← heU q, h1, h2, he01]
  · apply le_antisymm
    · rintro _ ⟨p, rfl⟩; exact ⟨_, rfl⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨e s, hge s s.2⟩

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {F : ℝ → ℝ → Plane}
/-! ## Periodicity -/
theorem per_sub_floor (periodic : ∀ r t, F r (t + 1) = F r t) (r x a : ℝ) :
    F r (x - ⌊a⌋) = F r x := by
  have hp : Function.Periodic (F r) 1 := fun t => periodic r t
  have := hp.sub_int_mul_eq (x := x) ⌊a⌋
  rwa [mul_one] at this

theorem per_fract (periodic : ∀ r t, F r (t + 1) = F r t) (r x : ℝ) :
    F r x = F r (Int.fract x) := by
  rw [← Int.self_sub_floor, per_sub_floor periodic]

theorem inj_fract (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    {r s x y : ℝ} (hr : 0 < r) (hs : 0 < s) (h : F r x = F s y) :
    r = s ∧ Int.fract x = Int.fract y := by
  rw [per_fract periodic r x, per_fract periodic s y] at h
  have := injective
    (⟨hr, Int.fract_nonneg x, Int.fract_lt_one x⟩ : (r, Int.fract x) ∈ Set.Ioi 0 ×ˢ Set.Ico 0 1)
    (⟨hs, Int.fract_nonneg y, Int.fract_lt_one y⟩ : (s, Int.fract y) ∈ Set.Ioi 0 ×ˢ Set.Ico 0 1) h
  simp only [Prod.mk.injEq] at this
  exact this

theorem norm_param (periodic : ∀ r t, F r (t + 1) = F r t) (r t a : ℝ) :
    ∃ t' ∈ Set.Ico a (a + 1), F r t' = F r t := by
  refine ⟨t - ⌊t - a⌋, ⟨?_, ?_⟩, per_sub_floor periodic r t _⟩
  · have := Int.floor_le (t - a); linarith
  · have := Int.lt_floor_add_one (t - a); linarith

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
theorem fract_eq_imp {a b : ℝ} (h1 : a - b < 1) (h2 : b - a < 1)
    (h : Int.fract a = Int.fract b) : a = b := by
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h
  have hz1 : (z : ℝ) < 1 := by linarith
  have hz2 : (-1 : ℝ) < z := by linarith
  have : z < 1 := by exact_mod_cast hz1
  have : -1 < z := by exact_mod_cast hz2
  have hz0 : z = 0 := by omega
  subst hz0
  simp only [Int.cast_zero] at hz
  linarith

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
/-! ## The trace of the drawing -/
theorem trace_eq : D.trace Set.univ =
    Set.range D.vertex ∪ ⋃ (v : V) (w : V) (h : G.Adj v w), Set.range (D.arc h) := by
  ext p
  constructor
  · rintro (⟨⟨v, -⟩, rfl⟩ | hp)
    · exact Or.inl ⟨v, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨v, -⟩, ⟨w, -⟩, h, t, rfl⟩ := hp
      exact Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨h, t, rfl⟩⟩⟩)
  · rintro (⟨v, rfl⟩ | hp)
    · exact Or.inl ⟨⟨v, trivial⟩, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨v, w, h, t, rfl⟩ := hp
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨⟨v, trivial⟩, ⟨w, trivial⟩, h, t, rfl⟩

theorem trace_compact [Finite V] : IsCompact (D.trace Set.univ) := by
  rw [trace_eq]
  exact (Set.finite_range _).isCompact.union (isCompact_iUnion fun v => isCompact_iUnion
    fun w => isCompact_iUnion fun h => isCompact_range (D.arc h).continuous)

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
/-! ## The rectangle path in parameter space -/
/-- Radius coordinate of the three-sided rectangle path `[0,3] → [0,1] × [a,b]`. -/
noncomputable def pr (u : ℝ) : ℝ := min (min u 1) (3 - u)

/-- Angle coordinate of the three-sided rectangle path. -/
noncomputable def pt (a b u : ℝ) : ℝ := a + (b - a) * max 0 (min 1 (u - 1))

theorem pr_cont : Continuous pr := by
  unfold pr; fun_prop

theorem pt_cont (a b : ℝ) : Continuous (pt a b) := by
  unfold pt; fun_prop

theorem pr_nonneg {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 3) : 0 ≤ pr u := by
  unfold pr
  simp only [le_min_iff]
  exact ⟨⟨hu.1, zero_le_one⟩, by linarith [hu.2]⟩

theorem pr_le_one (u : ℝ) : pr u ≤ 1 :=
  min_le_of_left_le (min_le_right _ _)

theorem pt_mem {a b : ℝ} (hab : a ≤ b) (u : ℝ) : pt a b u ∈ Set.Icc a b := by
  unfold pt
  have h0 : 0 ≤ max 0 (min 1 (u - 1)) := le_max_left _ _
  have h1 : max 0 (min 1 (u - 1)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hba : 0 ≤ b - a := by linarith
  constructor
  · nlinarith
  · nlinarith

theorem pr_lt_one {a b u : ℝ} (h : pr u < 1) :
    pt a b u = a ∨ pt a b u = b := by
  unfold pt
  rcases lt_or_ge u 1 with h1 | h1
  · left
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · have h3 : 3 - u < 1 := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : pr u = 1 := by unfold pr; rw [min_eq_right h1, min_eq_left hc]
      linarith
    right
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    ring

theorem pr_eq_zero {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 3) (h : pr u = 0) : u = 0 ∨ u = 3 := by
  obtain ⟨hu0, hu3⟩ := hu
  unfold pr at h
  simp only [min_def] at h
  split_ifs at h <;> first | (left; linarith) | (right; linarith)

theorem poly_inj {a b u v : ℝ} (hab : a < b) (hu : u ∈ Set.Icc (0 : ℝ) 3)
    (hv : v ∈ Set.Icc (0 : ℝ) 3) (h1 : pr u = pr v) (h2 : pt a b u = pt a b v) : u = v := by
  obtain ⟨hu0, hu3⟩ := hu
  obtain ⟨hv0, hv3⟩ := hv
  unfold pt at h2
  have h2' : max 0 (min 1 (u - 1)) = max 0 (min 1 (v - 1)) :=
    mul_left_cancel₀ (sub_pos.2 hab).ne' (by linarith)
  unfold pr at h1
  simp only [min_def, max_def] at h1 h2'
  split_ifs at h1 h2' <;> linarith

theorem pr_pt_r (a b : ℝ) {r : ℝ} (hr1 : r ≤ 1) :
    pr r = r ∧ pt a b r = a := by
  constructor
  · unfold pr; rw [min_eq_left hr1, min_eq_left (by linarith)]
  · unfold pt; rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring

theorem pr_pt_3r (a b : ℝ) {r : ℝ} (hr1 : r ≤ 1) :
    pr (3 - r) = r ∧ pt a b (3 - r) = b := by
  constructor
  · unfold pr; rw [min_eq_right (by linarith : (1 : ℝ) ≤ 3 - r), sub_sub_cancel,
      min_eq_right hr1]
  · unfold pt; rw [min_eq_left (by linarith), max_eq_right zero_le_one]; ring

theorem pr_pt_mid {a b t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    pr (1 + (t - a) / (b - a)) = 1 ∧ pt a b (1 + (t - a) / (b - a)) = t := by
  have hba : 0 < b - a := sub_pos.2 hab
  have m0 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hba.le
  have m1 : (t - a) / (b - a) ≤ 1 := (div_le_one hba).2 (by linarith [ht.2])
  constructor
  · unfold pr
    rw [min_eq_right (by linarith : (1 : ℝ) ≤ 1 + (t - a) / (b - a)),
      min_eq_left (by linarith : (1 : ℝ) ≤ 3 - (1 + (t - a) / (b - a)))]
  · unfold pt
    rw [add_sub_cancel_left, min_eq_right m1, max_eq_right m0]
    field_simp
    ring

theorem mid_mem {a b t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    1 + (t - a) / (b - a) ∈ Set.Icc (0 : ℝ) 3 := by
  have hba : 0 < b - a := sub_pos.2 hab
  have m0 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hba.le
  have m1 : (t - a) / (b - a) ≤ 1 := (div_le_one hba).2 (by linarith [ht.2])
  constructor <;> linarith

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-! ## The Jordan curve through the pinch point -/
theorem setup (h : Hyp D F) {s₁ s₂ : ℝ} (h12 : s₁ < s₂) (h21 : s₂ < s₁ + 1)
    (heq : F 0 s₁ = F 0 s₂) :
    ∃ I O J : Set Plane, IsOpen I ∧ IsOpen O ∧ Disjoint I O ∧ IsPreconnected I ∧
      IsCompact J ∧ I ∪ O = Jᶜ ∧ F 0 s₁ ∈ J ∧ J ∩ D.trace Set.univ ⊆ {F 0 s₁} ∧
      D.trace Set.univ \ {F 0 s₁} ⊆ I ∪ O ∧
      F 0 '' Set.Ioo s₁ s₂ \ {F 0 s₁} ⊆ I ∧
      F 0 '' Set.Ioo s₂ (s₁ + 1) \ {F 0 s₁} ⊆ O ∧
      (I ∩ D.outerFace Set.univ).Nonempty ∧
      (∀ t, F 0 t ∈ I → ∃ t' ∈ Set.Icc s₁ s₂, F 0 t' = F 0 t) := by
  obtain ⟨-, -, continuous, periodic, injective, onto, boundary, -⟩ := h
  set K := D.trace Set.univ with hK
  set Ω := D.outerFace Set.univ with hΩ
  have hKc : IsClosed K := (trace_compact D).isClosed
  have hmemΩ : ∀ z, z ∈ Ω ↔ z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) :=
    fun z => Iff.rfl
  have hcompΩ : ∀ z ∈ Ω, connectedComponentIn Kᶜ z ⊆ Ω := by
    intro z hz w hw
    have e := connectedComponentIn_eq hw
    rw [hmemΩ] at hz ⊢
    refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
    rw [← e]
    exact hz.2
  have hΩopen : IsOpen Ω := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn Kᶜ z, hcompΩ z hz,
      hKc.isOpen_compl.connectedComponentIn, mem_connectedComponentIn ((hmemΩ z).1 hz).1⟩
  have hfrK : frontier Ω ⊆ K := by
    intro q hq
    by_contra hqK
    rw [hΩopen.frontier_eq] at hq
    obtain ⟨z, hzC, hzΩ⟩ := mem_closure_iff.1 hq.1 (connectedComponentIn Kᶜ q)
      hKc.isOpen_compl.connectedComponentIn (mem_connectedComponentIn hqK)
    apply hq.2
    rw [hmemΩ] at hzΩ ⊢
    refine ⟨hqK, ?_⟩
    rw [connectedComponentIn_eq hzC]
    exact hzΩ.2
  have hΩK : ∀ z ∈ Ω, z ∉ K := fun z hz => ((hmemΩ z).1 hz).1
  have hF0 : ∀ t, F 0 t ∈ K := fun t => hfrK (by rw [← boundary]; exact ⟨t, rfl⟩)
  have hFΩ : ∀ r t, 0 < r → F r t ∈ Ω := by
    intro r t hr
    rw [← onto]
    exact ⟨(r, t), ⟨hr, trivial⟩, rfl⟩
  -- the loop in parameter space
  obtain ⟨g, hg⟩ : ∃ g : ℝ → Plane, g = fun u => F (pr u) (pt s₁ s₂ u) := ⟨_, rfl⟩
  have hgdef : ∀ u, g u = F (pr u) (pt s₁ s₂ u) := by intro u; rw [hg]
  have hgc : ContinuousOn g (Set.Icc 0 3) := by
    have : ContinuousOn (fun u : ℝ => (pr u, pt s₁ s₂ u)) (Set.Icc 0 3) :=
      (pr_cont.prodMk (pt_cont s₁ s₂)).continuousOn
    rw [hg]
    exact continuous.comp this (fun u hu => ⟨pr_nonneg hu, trivial⟩)
  have hptm : ∀ u, pt s₁ s₂ u ∈ Set.Icc s₁ s₂ := pt_mem h12.le
  have hg0 : ∀ u ∈ Set.Icc (0 : ℝ) 3, pr u = 0 → g u = F 0 s₁ := by
    intro u _ h0
    rw [hgdef]
    rcases pr_lt_one (a := s₁) (b := s₂) (u := u) (by rw [h0]; exact zero_lt_one) with e | e <;>
      rw [h0, e]
    exact heq.symm
  set J := g '' Set.Icc 0 3 with hJ
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hgc
  have hxJ : F 0 s₁ ∈ J :=
    ⟨0, ⟨le_refl _, by norm_num⟩, hg0 0 ⟨le_refl _, by norm_num⟩ (by unfold pr; norm_num)⟩
  have hJ_cases : ∀ z ∈ J, z = F 0 s₁ ∨ z ∈ Ω := by
    rintro _ ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le (pr_nonneg hu) with h0 | hpos
    · exact Or.inl (hg0 u hu h0.symm)
    · rw [hgdef]; exact Or.inr (hFΩ _ _ hpos)
  have hJK : J ∩ K ⊆ {F 0 s₁} := by
    rintro z ⟨hzJ, hzK⟩
    rcases hJ_cases z hzJ with e | e
    · exact e
    · exact absurd hzK (hΩK z e)
  have hJparam : ∀ r t, 0 < r → F r t ∈ J → ∃ u ∈ Set.Icc (0 : ℝ) 3,
      pr u = r ∧ Int.fract t = Int.fract (pt s₁ s₂ u) := by
    rintro r t hr ⟨u, hu, he⟩
    rcases eq_or_lt_of_le (pr_nonneg hu) with h0 | hpos
    · exact absurd (show F r t ∈ K by rw [← he, hg0 u hu h0.symm]; exact hF0 s₁)
        (hΩK _ (hFΩ r t hr))
    · rw [hgdef] at he
      obtain ⟨e1, e2⟩ := inj_fract periodic injective hr hpos he.symm
      exact ⟨u, hu, e1.symm, e2⟩
  -- the two regions
  set Sin := Function.uncurry F '' (Set.Ioo 0 1 ×ˢ Set.Ioo s₁ s₂) with hSin
  set Pout : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo s₂ (s₁ + 1) ∪ Set.Ioi 1 ×ˢ Set.univ
    with hPout
  set Sout := Function.uncurry F '' Pout with hSout
  have hSinJ : ∀ z ∈ Sin, z ∉ J := by
    rintro _ ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩ hJ'
    obtain ⟨u, hu, e1, e2⟩ := hJparam r t hr.1 hJ'
    rcases pr_lt_one (a := s₁) (b := s₂) (u := u) (by rw [e1]; exact hr.2) with e | e
    · rw [e] at e2
      have := fract_eq_imp (by linarith [ht.1, ht.2]) (by linarith [ht.1, ht.2]) e2
      linarith [ht.1]
    · rw [e] at e2
      have := fract_eq_imp (by linarith [ht.1, ht.2]) (by linarith [ht.1, ht.2]) e2
      linarith [ht.2]
  have hSoutJ : ∀ z ∈ Sout, z ∉ J := by
    rintro _ ⟨⟨r, t⟩, hrt, rfl⟩ hJ'
    have hr : 0 < r := by
      rcases hrt with ⟨hr, -⟩ | ⟨hr, -⟩
      · exact hr
      · exact lt_trans zero_lt_one hr
    obtain ⟨u, hu, e1, e2⟩ := hJparam r t hr hJ'
    have hp := hptm u
    rcases hrt with ⟨-, ht⟩ | ⟨hr1, -⟩
    · have := fract_eq_imp (by linarith [ht.2, hp.1]) (by linarith [ht.1, hp.2]) e2
      linarith [ht.1, hp.2]
    · have := pr_le_one u
      have : (1 : ℝ) < r := hr1
      linarith
  have hSinpre : IsPreconnected Sin :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
      (continuous.mono (fun p (hp : p ∈ Set.Ioo 0 1 ×ˢ Set.Ioo s₁ s₂) =>
        ⟨le_of_lt hp.1.1, trivial⟩))
  have hPoutsub : Pout ⊆ Set.Ici 0 ×ˢ Set.univ := by
    rintro ⟨r, t⟩ (⟨hr, -⟩ | ⟨hr, -⟩)
    · exact ⟨le_of_lt (Set.mem_Ioi.1 hr), trivial⟩
    · have : (1 : ℝ) < r := hr
      exact ⟨show (0 : ℝ) ≤ r by linarith, trivial⟩
  have hPoutpre : IsPreconnected Pout := by
    refine IsPreconnected.union ((2 : ℝ), (s₂ + (s₁ + 1)) / 2)
      (s := Set.Ioi 0 ×ˢ Set.Ioo s₂ (s₁ + 1)) (t := Set.Ioi 1 ×ˢ Set.univ) ?_ ?_
      (isPreconnected_Ioi.prod isPreconnected_Ioo) (isPreconnected_Ioi.prod isPreconnected_univ)
    · exact ⟨show (0 : ℝ) < 2 by norm_num,
        show s₂ < (s₂ + (s₁ + 1)) / 2 ∧ (s₂ + (s₁ + 1)) / 2 < s₁ + 1 by
          constructor <;> linarith⟩
    · exact ⟨show (1 : ℝ) < 2 by norm_num, trivial⟩
  have hSoutpre : IsPreconnected Sout := hPoutpre.image _ (continuous.mono hPoutsub)
  -- the Jordan curve
  have hmem3 : ∀ s : unitInterval, 3 * (s : ℝ) ∈ Set.Icc (0 : ℝ) 3 := by
    intro s
    have := s.2.1
    have := s.2.2
    constructor <;> linarith
  obtain ⟨g', hg'c, hg'i, hg'r⟩ := circle_param (f := fun s : unitInterval => g (3 * (s : ℝ)))
    (hgc.comp_continuous (continuous_const.mul continuous_subtype_val) hmem3) (by
      show g (3 * ((0 : unitInterval) : ℝ)) = g (3 * ((1 : unitInterval) : ℝ))
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
      rw [hg0 0 ⟨le_refl _, by norm_num⟩ (by unfold pr; norm_num),
        hg0 3 ⟨by norm_num, le_refl _⟩ (by unfold pr; norm_num)]) (by
      intro s t hst
      change g (3 * (s : ℝ)) = g (3 * (t : ℝ)) at hst
      have hu := hmem3 s
      have hv := hmem3 t
      rcases eq_or_lt_of_le (pr_nonneg hu) with hu0 | hupos <;>
        rcases eq_or_lt_of_le (pr_nonneg hv) with hv0 | hvpos
      · rcases pr_eq_zero hu hu0.symm with a | a <;> rcases pr_eq_zero hv hv0.symm with b | b
        · exact Or.inl (Subtype.ext (by linarith))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
        · exact Or.inl (Subtype.ext (by linarith))
      · exfalso
        apply hΩK _ (hFΩ (pr (3 * (t : ℝ))) (pt s₁ s₂ (3 * (t : ℝ))) hvpos)
        rw [← hgdef, ← hst, hg0 _ hu hu0.symm]
        exact hF0 s₁
      · exfalso
        apply hΩK _ (hFΩ (pr (3 * (s : ℝ))) (pt s₁ s₂ (3 * (s : ℝ))) hupos)
        rw [← hgdef, hst, hg0 _ hv hv0.symm]
        exact hF0 s₁
      · rw [hgdef, hgdef] at hst
        obtain ⟨e1, e2⟩ := inj_fract periodic injective hupos hvpos hst
        have hp1 := hptm (3 * (s : ℝ))
        have hp2 := hptm (3 * (t : ℝ))
        have e3 := fract_eq_imp (by linarith [hp1.2, hp2.1]) (by linarith [hp2.2, hp1.1]) e2
        have := poly_inj h12 hu hv e1 e3
        exact Or.inl (Subtype.ext (by linarith)))
  have hrf : Set.range (fun s : unitInterval => g (3 * (s : ℝ))) = J := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨3 * (s : ℝ), hmem3 s, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨u / 3, by constructor <;> linarith [hu.1, hu.2]⟩, ?_⟩
      show g (3 * (u / 3)) = g u
      congr 1
      ring
  rw [hrf] at hg'r
  let φ : ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) := planeHomeo.symm
  obtain ⟨I, O, hIo, hOo, hIc, -, hIb, -, hdisj, hun, hfI, -⟩ :=
    JordanCurve.jordan_curve_theorem (φ ∘ g') (φ.continuous.comp hg'c)
      (φ.injective.comp hg'i)
  have hrange : φ ⁻¹' Set.range (φ ∘ g') = J := by
    rw [Set.range_comp, Set.preimage_image_eq _ φ.injective, hg'r]
  set I' := φ ⁻¹' I with hI'
  set O' := φ ⁻¹' O with hO'
  have hI'o : IsOpen I' := hIo.preimage φ.continuous
  have hO'o : IsOpen O' := hOo.preimage φ.continuous
  have hdisj' : Disjoint I' O' := hdisj.preimage φ
  have hun' : I' ∪ O' = Jᶜ := by
    rw [hI', hO', ← Set.preimage_union, hun, Set.preimage_compl, hrange]
  have hJcl : J ⊆ closure I' := by
    intro x hx
    rw [hI', ← φ.preimage_closure]
    have : x ∈ φ ⁻¹' frontier I := by rw [hfI, hrange]; exact hx
    exact frontier_subset_closure this
  have heI : I' = planeHomeo '' I := congrFun (Homeomorph.preimage_symm planeHomeo) I
  have hI'b : Bornology.IsBounded I' := by
    rw [heI]
    exact (hIb.isCompact_closure.image planeHomeo.continuous).isBounded.subset
      (Set.image_mono subset_closure)
  have hI'pre : IsPreconnected I' := by
    rw [heI]
    exact hIc.isPreconnected.image _ planeHomeo.continuous.continuousOn
  have hI'J : ∀ z ∈ I', z ∉ J := by
    intro z hz hzJ
    have : z ∈ I' ∪ O' := Or.inl hz
    rw [hun'] at this
    exact this hzJ
  have hO'J : ∀ z ∈ O', z ∉ J := by
    intro z hz hzJ
    have : z ∈ I' ∪ O' := Or.inr hz
    rw [hun'] at this
    exact this hzJ
  have hclI : closure I' ⊆ I' ∪ J := by
    intro z hz
    have hzO : z ∈ O'ᶜ := closure_minimal (fun w hw => Set.disjoint_left.1 hdisj' hw)
      hO'o.isClosed_compl hz
    by_cases hzJ : z ∈ J
    · exact Or.inr hzJ
    · have : z ∈ I' ∪ O' := by rw [hun']; exact hzJ
      rcases this with h | h
      · exact Or.inl h
      · exact absurd h hzO
  have hclO : closure O' ⊆ O' ∪ J := by
    intro z hz
    have hzI : z ∈ I'ᶜ := closure_minimal (fun w hw => Set.disjoint_right.1 hdisj' hw)
      hI'o.isClosed_compl hz
    by_cases hzJ : z ∈ J
    · exact Or.inr hzJ
    · have : z ∈ I' ∪ O' := by rw [hun']; exact hzJ
      rcases this with h | h
      · exact absurd h hzI
      · exact Or.inl h
  have hSinIO : Sin ⊆ I' ∪ O' := by rw [hun']; exact hSinJ
  have hSoutIO : Sout ⊆ I' ∪ O' := by rw [hun']; exact hSoutJ
  -- Ω is unbounded
  have hΩunb : ¬ Bornology.IsBounded Ω := by
    have hz0 : F 1 0 ∈ Ω := hFΩ 1 0 one_pos
    intro hb
    exact ((hmemΩ _).1 hz0).2 (hb.subset (hcompΩ _ hz0))
  have hΩsub : Ω ⊆ Function.uncurry F '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ∪ Sout := by
    intro z hz
    rw [← onto] at hz
    obtain ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩ := hz
    have hs' : 0 < s := hs
    rcases le_or_gt s 1 with h | h
    · exact Or.inl ⟨(s, Int.fract t), ⟨⟨hs'.le, h⟩, Int.fract_nonneg t,
        (Int.fract_lt_one t).le⟩, (per_fract periodic s t).symm⟩
    · exact Or.inr ⟨(s, t), Or.inr ⟨h, trivial⟩, rfl⟩
  have hBc : IsCompact (Function.uncurry F '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (continuous.mono (Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)))
  have hSoutO : Sout ⊆ O' := by
    rcases hSoutpre.subset_or_subset hI'o hO'o hdisj' hSoutIO with h | h
    · exact absurd ((hBc.isBounded.union (hI'b.subset h)).subset hΩsub) hΩunb
    · exact h
  have hSinI : Sin ⊆ I' := by
    rcases hSinpre.subset_or_subset hI'o hO'o hdisj' hSinIO with h | h
    · exact h
    · exfalso
      have hmid : (s₁ + s₂) / 2 ∈ Set.Icc s₁ s₂ := ⟨by linarith, by linarith⟩
      have hy : F 1 ((s₁ + s₂) / 2) ∈ J := ⟨_, mid_mem h12 hmid, by
        rw [hgdef, (pr_pt_mid h12 hmid).1, (pr_pt_mid h12 hmid).2]⟩
      obtain ⟨w, hwΩ, hwI⟩ := mem_closure_iff.1 (hJcl hy) Ω hΩopen (hFΩ 1 _ one_pos)
      have hwJ : w ∉ J := hI'J w hwI
      rw [← onto] at hwΩ
      obtain ⟨⟨r, t⟩, ⟨hr, -⟩, rfl⟩ := hwΩ
      have hr' : 0 < r := hr
      obtain ⟨t', ht', he⟩ := norm_param periodic r t s₁
      change F r t ∈ I' at hwI
      change F r t ∉ J at hwJ
      rw [← he] at hwI hwJ
      have key : F r t' ∈ Sin ∨ F r t' ∈ Sout ∨ F r t' ∈ J := by
        by_cases hr1 : 1 < r
        · exact Or.inr (Or.inl ⟨(r, t'), Or.inr ⟨hr1, trivial⟩, rfl⟩)
        replace hr1 := not_lt.1 hr1
        by_cases ht2 : s₂ < t'
        · exact Or.inr (Or.inl ⟨(r, t'), Or.inl ⟨hr', ht2, ht'.2⟩, rfl⟩)
        replace ht2 := not_lt.1 ht2
        rcases eq_or_lt_of_le ht'.1 with e | e
        · refine Or.inr (Or.inr ⟨r, ⟨hr'.le, by linarith⟩, ?_⟩)
          rw [hgdef, (pr_pt_r s₁ s₂ hr1).1, (pr_pt_r s₁ s₂ hr1).2, e]
        rcases eq_or_lt_of_le ht2 with e2 | e2
        · refine Or.inr (Or.inr ⟨3 - r, ⟨by linarith, by linarith⟩, ?_⟩)
          rw [hgdef, (pr_pt_3r s₁ s₂ hr1).1, (pr_pt_3r s₁ s₂ hr1).2, e2]
        rcases eq_or_lt_of_le hr1 with e3 | e3
        · have hm : t' ∈ Set.Icc s₁ s₂ := ⟨e.le, ht2⟩
          refine Or.inr (Or.inr ⟨_, mid_mem h12 hm, ?_⟩)
          rw [hgdef, (pr_pt_mid h12 hm).1, (pr_pt_mid h12 hm).2, e3]
        · exact Or.inl ⟨(r, t'), ⟨⟨hr', e3⟩, ⟨e, e2⟩⟩, rfl⟩
      rcases key with k | k | k
      · exact Set.disjoint_left.1 hdisj' hwI (h k)
      · exact Set.disjoint_left.1 hdisj' hwI (hSoutO k)
      · exact hwJ k
  -- boundary values
  have hψlim : ∀ t, ∀ P : Set (ℝ × ℝ), (∀ r ∈ Set.Ioo (0 : ℝ) 1, (r, t) ∈ P) →
      F 0 t ∈ closure (Function.uncurry F '' P) := by
    intro t P hP
    have hc : ContinuousWithinAt (fun r => F r t) (Set.Ioo 0 1) 0 := by
      have : ContinuousOn (fun r => F r t) (Set.Ici 0) :=
        continuous.comp (Continuous.continuousOn (f := fun r : ℝ => (r, t)) (by fun_prop)) (fun r hr => ⟨hr, trivial⟩)
      exact (this 0 (Set.mem_Ici.2 le_rfl)).mono (fun r hr => Set.mem_Ici.2 (le_of_lt hr.1))
    have h1 := hc.mem_closure_image
      (by rw [closure_Ioo zero_ne_one]; exact Set.left_mem_Icc.2 zero_le_one)
    refine closure_mono ?_ h1
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨(r, t), hP r hr, rfl⟩
  have hψin : ∀ t ∈ Set.Ioo s₁ s₂, F 0 t ∈ I' ∪ J := fun t ht =>
    hclI (closure_mono hSinI (hψlim t _ (fun r hr => ⟨hr, ht⟩)))
  have hψout : ∀ t ∈ Set.Ioo s₂ (s₁ + 1), F 0 t ∈ O' ∪ J := fun t ht =>
    hclO (closure_mono hSoutO (hψlim t _ (fun r hr => Or.inl ⟨hr.1, ht⟩)))
  refine ⟨I', O', J, hI'o, hO'o, hdisj', hI'pre, hJc, hun', hxJ, hJK, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzK, hzx⟩
    rw [hun']
    intro hzJ
    exact hzx (hJK ⟨hzJ, hzK⟩)
  · rintro _ ⟨⟨t, ht, rfl⟩, hne⟩
    rcases hψin t ht with k | k
    · exact k
    · exact absurd (hJK ⟨k, hF0 t⟩) hne
  · rintro _ ⟨⟨t, ht, rfl⟩, hne⟩
    rcases hψout t ht with k | k
    · exact k
    · exact absurd (hJK ⟨k, hF0 t⟩) hne
  · refine ⟨F (1 / 2) ((s₁ + s₂) / 2), hSinI ⟨(1 / 2, (s₁ + s₂) / 2),
      ⟨⟨by norm_num, by norm_num⟩, by constructor <;> linarith⟩, rfl⟩, hFΩ _ _ (by norm_num)⟩
  · intro t ht
    obtain ⟨t', ht', he⟩ := norm_param periodic 0 t s₁
    by_cases h2 : t' ≤ s₂
    · exact ⟨t', ⟨ht'.1, h2⟩, he⟩
    · exfalso
      rcases hψout t' ⟨lt_of_not_ge h2, ht'.2⟩ with k | k
      · rw [he] at k; exact Set.disjoint_left.1 hdisj' ht k
      · rw [he] at k; exact hI'J _ ht k

/-- Two boundary parameters with the same point cut the drawing minus that point into the
part reached between them and the part reached after them. -/
theorem cut (h : Hyp D F) {s₁ s₂ : ℝ} (h12 : s₁ < s₂) (h21 : s₂ < s₁ + 1)
    (heq : F 0 s₁ = F 0 s₂) :
    ∃ U W : Set Plane, IsOpen U ∧ IsOpen W ∧ Disjoint U W ∧
      D.trace Set.univ \ {F 0 s₁} ⊆ U ∪ W ∧
      F 0 '' Set.Ioo s₁ s₂ \ {F 0 s₁} ⊆ U ∧
      F 0 '' Set.Ioo s₂ (s₁ + 1) \ {F 0 s₁} ⊆ W := by
  obtain ⟨I, O, -, hIo, hOo, hd, -, -, -, -, -, hK, hin, hout, -, -⟩ := setup h h12 h21 heq
  exact ⟨I, O, hIo, hOo, hd, hK, hin, hout⟩

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias cut := OuterplanarL1Tan.Dev.FR.PartJ.cut

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartJ
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-- A boundary loop inside a non-separating compact part `A` of the drawing traps every
connected piece of the drawing (minus the base point) that it touches. -/
theorem no_small_loop (h : Hyp D F) {s₁ s₂ : ℝ} (h12 : s₁ < s₂) (h21 : s₂ < s₁ + 1)
    (heq : F 0 s₁ = F 0 s₂) (A : Set Plane) (hA : IsCompact A)
    (hAK : A ⊆ D.trace Set.univ) (hAc : IsPreconnected Aᶜ)
    (hψA : F 0 '' Set.Icc s₁ s₂ ⊆ A) (C : Set Plane) (hC : IsPreconnected C)
    (hCK : C ⊆ D.trace Set.univ \ {F 0 s₁})
    (hCm : (C ∩ F 0 '' Set.Ioo s₁ s₂).Nonempty) : C ⊆ A := by
  obtain ⟨I, O, J, hIo, hOo, hd, hIpre, hJc, hun, hxJ, hJK, hK, hin, -, hIΩ, hψI⟩ :=
    setup h h12 h21 heq
  have hboundary := h.bdry
  set K := D.trace Set.univ with hKdef
  set Ω := D.outerFace Set.univ with hΩ
  have hΩK : ∀ z ∈ Ω, z ∉ K := fun z hz => hz.1
  have hxA : F 0 s₁ ∈ A := hψA ⟨s₁, ⟨le_refl _, h12.le⟩, rfl⟩
  have hJA : J ∩ A = {F 0 s₁} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzJ, hzA⟩
      exact hJK ⟨hzJ, hAK hzA⟩
    · rintro z rfl
      exact ⟨hxJ, hxA⟩
  -- `I` is a component of `Jᶜ`
  obtain ⟨q, hqI, hqΩ⟩ := hIΩ
  have hIcomp : connectedComponentIn Jᶜ q = I := by
    apply Set.Subset.antisymm
    · have hsub : connectedComponentIn Jᶜ q ⊆ I ∪ O := by
        rw [hun]; exact connectedComponentIn_subset _ _
      have hqJ : q ∉ J := by
        intro hqJ
        have : q ∈ I ∪ O := Or.inl hqI
        rw [hun] at this
        exact this hqJ
      rcases isPreconnected_connectedComponentIn.subset_or_subset hIo hOo hd hsub with k | k
      · exact k
      · exact absurd (k (mem_connectedComponentIn hqJ)) (Set.disjoint_left.1 hd hqI)
    · exact hIpre.subset_connectedComponentIn hqI (by rw [← hun]; exact Set.subset_union_left)
  have hT : IsPreconnected (I \ A) := by
    have := compact_singleton_attachment_region_preconnected J A (F 0 s₁) q hJc hA hJA hAc
    rwa [hIcomp] at this
  -- Ω is open (Ω ∩ I is the open piece we use)
  have hKc : IsClosed K := (trace_compact D).isClosed
  have hmemΩ : ∀ z, z ∈ Ω ↔ z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) :=
    fun z => Iff.rfl
  have hcompΩ : ∀ z ∈ Ω, connectedComponentIn Kᶜ z ⊆ Ω := by
    intro z hz w hw
    have e := connectedComponentIn_eq hw
    rw [hmemΩ] at hz ⊢
    refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
    rw [← e]
    exact hz.2
  have hΩopen : IsOpen Ω := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn Kᶜ z, hcompΩ z hz,
      hKc.isOpen_compl.connectedComponentIn, mem_connectedComponentIn ((hmemΩ z).1 hz).1⟩
  have hTsub : I \ A ⊆ Ω ∩ I := by
    apply hT.subset_of_closure_inter_subset (hΩopen.inter hIo)
    · refine ⟨q, ⟨hqI, ?_⟩, hqΩ, hqI⟩
      intro hqA
      exact hΩK q hqΩ (hAK hqA)
    · rintro y ⟨hycl, hyI, hyA⟩
      refine ⟨?_, hyI⟩
      by_contra hyΩ
      have hyfr : y ∈ frontier Ω := by
        rw [hΩopen.frontier_eq]
        exact ⟨closure_mono Set.inter_subset_left hycl, hyΩ⟩
      rw [← hboundary] at hyfr
      obtain ⟨t, rfl⟩ := hyfr
      obtain ⟨t', ht', he⟩ := hψI t hyI
      exact hyA (he ▸ hψA ⟨t', ht', rfl⟩)
  -- `C` lies inside
  obtain ⟨c, hcC, hcψ⟩ := hCm
  have hCI : C ⊆ I := by
    apply hC.subset_left_of_subset_union hIo hOo hd (hCK.trans hK)
    exact ⟨c, hcC, hin ⟨hcψ, (hCK hcC).2⟩⟩
  intro z hz
  by_contra hzA
  have := (hTsub ⟨hCI hz, hzA⟩).1
  exact hΩK z this (hCK hz).1

end OuterplanarL1Tan.Dev.FR.PartJ
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias no_small_loop := OuterplanarL1Tan.Dev.FR.PartJ.no_small_loop

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
/-- A homeomorphism between the plane `ℝ × ℝ` and Euclidean space. -/
noncomputable def planeHomeo : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
variable {X : Type*} [TopologicalSpace X]
/-! ## Paths -/
theorem ext_inj {a b : X} (γ : Path a b) (hγ : Function.Injective γ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (h : γ.extend x = γ.extend y) : x = y := by
  rw [Path.extend_apply γ hx, Path.extend_apply γ hy] at h
  exact congrArg Subtype.val (hγ h)

theorem ext_symm {a b : X} (γ : Path a b) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    γ.symm.extend x = γ.extend (1 - x) := by
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [Path.extend_apply _ hx, Path.extend_apply _ hx']
  rfl

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
/-- A sub-arc of an injective path in the plane does not separate the plane. -/
theorem subarc_compl {a b : Plane} (γ : Path a b) (hγ : Function.Injective γ) {s t : ℝ}
    (h0 : 0 ≤ s) (hst : s < t) (h1 : t ≤ 1) : IsPreconnected (γ.extend '' Icc s t)ᶜ := by
  let α : Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun u => planeHomeo.symm (γ.extend (s + (t - s) * u))
  have hc : Continuous α :=
    planeHomeo.symm.continuous.comp (γ.continuous_extend.comp (by fun_prop))
  have hmem : ∀ u : Icc (0 : ℝ) 1, s + (t - s) * (u : ℝ) ∈ Icc (0 : ℝ) 1 := by
    intro u
    have := u.2.1; have := u.2.2
    constructor <;> nlinarith
  have hinj : Function.Injective α := by
    intro u u' huu
    have h' := planeHomeo.symm.injective huu
    have := ext_inj γ hγ (hmem u) (hmem u') h'
    have hts : (t - s) ≠ 0 := by linarith
    apply Subtype.ext
    have : (t - s) * (u : ℝ) = (t - s) * u' := by linarith
    exact mul_left_cancel₀ hts this
  have hrange : Set.range α = planeHomeo.symm '' (γ.extend '' Icc s t) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨γ.extend (s + (t - s) * u), ⟨s + (t - s) * u, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · have := u.2.1; nlinarith
      · have := u.2.2; nlinarith
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hts : 0 < t - s := by linarith
      refine ⟨⟨(x - s) / (t - s), ⟨div_nonneg (by linarith [hx.1]) hts.le,
        (div_le_one hts).2 (by linarith [hx.2])⟩⟩, ?_⟩
      simp only [α]
      congr 2
      field_simp
      ring
  have hcon := (JordanCurve.simple_arc_complement_connected α hc hinj).isPreconnected
  have heq : (γ.extend '' Icc s t)ᶜ = planeHomeo '' (Set.range α)ᶜ := by
    rw [hrange, Set.image_compl_eq planeHomeo.bijective]
    congr 1
    ext z; simp
  rw [heq]
  exact hcon.image _ planeHomeo.continuous.continuousOn

theorem isClosed_imp {P : Prop} {s : Set ℝ} (hs : IsClosed s) : IsClosed {t | P → t ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
/-! ## The trace of the drawing -/
theorem trace_eq : D.trace Set.univ =
    Set.range D.vertex ∪ ⋃ (v : V) (w : V) (h : G.Adj v w), Set.range (D.arc h) := by
  ext p
  constructor
  · rintro (⟨⟨v, -⟩, rfl⟩ | hp)
    · exact Or.inl ⟨v, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨v, -⟩, ⟨w, -⟩, h, t, rfl⟩ := hp
      exact Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨h, t, rfl⟩⟩⟩)
  · rintro (⟨v, rfl⟩ | hp)
    · exact Or.inl ⟨⟨v, trivial⟩, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨v, w, h, t, rfl⟩ := hp
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨⟨v, trivial⟩, ⟨w, trivial⟩, h, t, rfl⟩

theorem trace_compact [Finite V] : IsCompact (D.trace Set.univ) := by
  rw [trace_eq]
  exact (Set.finite_range _).isCompact.union (isCompact_iUnion fun v => isCompact_iUnion
    fun w => isCompact_iUnion fun h => isCompact_range (D.arc h).continuous)

theorem ext_mem_trace {v w : V} (e : G.Adj v w) (x : ℝ) :
    (D.arc e).extend x ∈ D.trace Set.univ := by
  rw [trace_eq]
  refine Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨e, ?_⟩⟩⟩)
  exact ⟨_, rfl⟩

/-- Germ at an interior point of an edge. -/
theorem germ_edge [Finite V] {v w : V} (e : G.Adj v w) {σ η : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hη : 0 < η) :
    ∃ N : Set Plane, IsOpen N ∧ (D.arc e).extend σ ∈ N ∧
      D.trace Set.univ ∩ N ⊆ (D.arc e).extend '' Ioo (σ - η) (σ + η) := by
  set g := (D.arc e).extend with hg
  have hσI : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ0.le, hσ1.le⟩
  let J : V → V → Set ℝ := fun x y => Icc 0 1 ∩ {t | x = v ∧ y = w → t ∈ (Ioo (σ - η) (σ + η))ᶜ}
    ∩ {t | x = w ∧ y = v → t ∈ (fun t => 1 - t) ⁻¹' (Ioo (σ - η) (σ + η))ᶜ}
  have hJc : ∀ x y, IsCompact (J x y) := by
    intro x y
    refine isCompact_Icc.of_isClosed_subset ?_ (fun t ht => ht.1.1)
    refine (isClosed_Icc.inter (isClosed_imp isOpen_Ioo.isClosed_compl)).inter
      (isClosed_imp (isOpen_Ioo.isClosed_compl.preimage (by fun_prop)))
  let Q : Set Plane := Set.range D.vertex ∪
    ⋃ (x : V) (y : V) (e' : G.Adj x y), (D.arc e').extend '' J x y
  have hQ : IsCompact Q := (Set.finite_range _).isCompact.union (isCompact_iUnion fun x =>
    isCompact_iUnion fun y => isCompact_iUnion fun e' =>
      (hJc x y).image (D.arc e').continuous_extend)
  refine ⟨Qᶜ, hQ.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro (⟨x, hx⟩ | hq)
    · have hx' : D.vertex x = D.arc e ⟨σ, hσI⟩ := by rw [hx, hg, Path.extend_apply _ hσI]
      rcases D.arc_avoids_vertices e ⟨σ, hσI⟩ x hx'.symm with rfl | rfl
      · rw [← (D.arc e).extend_zero] at hx
        have := ext_inj _ (D.arc_injective e) ⟨le_rfl, zero_le_one⟩ hσI hx
        linarith
      · rw [← (D.arc e).extend_one] at hx
        have := ext_inj _ (D.arc_injective e) ⟨zero_le_one, le_rfl⟩ hσI hx
        linarith
    · simp only [Set.mem_iUnion] at hq
      obtain ⟨x, y, e', t, htJ, hzt⟩ := hq
      have htI : t ∈ Icc (0 : ℝ) 1 := htJ.1.1
      have hzt' : D.arc e' ⟨t, htI⟩ = D.arc e ⟨σ, hσI⟩ := by
        rw [← Path.extend_apply _ htI, hzt, hg, Path.extend_apply _ hσI]
      rcases D.arcs_meet_only_at_endpoints e' e ⟨t, htI⟩ ⟨σ, hσI⟩ hzt' with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, h0 | h1⟩
      · have := ext_inj _ (D.arc_injective e) htI hσI hzt
        exact htJ.1.2 ⟨rfl, rfl⟩ ⟨by linarith, by linarith⟩
      · have hrev : D.arc e' = (D.arc e).symm := D.arc_reverse e
        rw [hrev, ext_symm _ htI] at hzt
        have h1t : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [htI.2], by linarith [htI.1]⟩
        have := ext_inj _ (D.arc_injective e) h1t hσI hzt
        exact htJ.2 ⟨rfl, rfl⟩ ⟨by simp only; linarith, by simp only; linarith⟩
      · have := congrArg Subtype.val h0; simp at this; linarith
      · have := congrArg Subtype.val h1; simp at this; linarith
  · rintro z ⟨hzK, hzN⟩
    rw [trace_eq] at hzK
    rcases hzK with ⟨x, rfl⟩ | hz
    · exact absurd (Or.inl ⟨x, rfl⟩) hzN
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨x, y, e', t, rfl⟩ := hz
      have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.2
      have hzt : D.arc e' t = (D.arc e').extend t := (Path.extend_extends' _ t).symm
      have htJ : (t : ℝ) ∈ J x y → False := fun hJ => hzN (Or.inr (Set.mem_iUnion.2 ⟨x,
        Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨e', (t : ℝ), hJ, hzt.symm⟩⟩⟩))
      have hvw : v ≠ w := G.ne_of_adj e
      by_cases c1 : x = v ∧ y = w
      · obtain ⟨rfl, rfl⟩ := c1
        by_cases hin : (t : ℝ) ∈ Ioo (σ - η) (σ + η)
        · exact ⟨t, hin, hzt.symm⟩
        · exact (htJ ⟨⟨htI, fun _ => hin⟩, fun hh => absurd hh.1 hvw⟩).elim
      by_cases c2 : x = w ∧ y = v
      · obtain ⟨rfl, rfl⟩ := c2
        have hrev : D.arc e' = (D.arc e).symm := D.arc_reverse e
        by_cases hin : 1 - (t : ℝ) ∈ Ioo (σ - η) (σ + η)
        · refine ⟨1 - t, hin, ?_⟩
          rw [hzt, hrev, ext_symm _ htI]
        · exact (htJ ⟨⟨htI, fun hh => absurd hh.1 (Ne.symm hvw)⟩, fun _ => hin⟩).elim
      · exact (htJ ⟨⟨htI, fun hh => absurd hh c1⟩, fun hh => absurd hh c2⟩).elim

/-- Germ at a vertex. -/
theorem germ_vertex [Finite V] (v : V) {η : ℝ} (hη0 : 0 < η) (_hη1 : η < 1) :
    ∃ N : Set Plane, IsOpen N ∧ D.vertex v ∈ N ∧
      D.trace Set.univ ∩ N ⊆ {D.vertex v} ∪
        ⋃ (w : V) (e : G.Adj v w), (D.arc e).extend '' Ioo 0 η := by
  let J : V → V → Set ℝ := fun x y => Icc 0 1 ∩ {t | x = v → t ∈ Ici η}
    ∩ {t | y = v → t ∈ Iic (1 - η)}
  have hJc : ∀ x y, IsCompact (J x y) := by
    intro x y
    refine isCompact_Icc.of_isClosed_subset ?_ (fun t ht => ht.1.1)
    exact (isClosed_Icc.inter (isClosed_imp isClosed_Ici)).inter (isClosed_imp isClosed_Iic)
  let Q : Set Plane := (Set.range D.vertex \ {D.vertex v}) ∪
    ⋃ (x : V) (y : V) (e' : G.Adj x y), (D.arc e').extend '' J x y
  have hQ : IsCompact Q := ((Set.finite_range _).sdiff).isCompact.union
    (isCompact_iUnion fun x => isCompact_iUnion fun y => isCompact_iUnion fun e' =>
      (hJc x y).image (D.arc e').continuous_extend)
  refine ⟨Qᶜ, hQ.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro (⟨-, hx⟩ | hq)
    · exact hx rfl
    · simp only [Set.mem_iUnion] at hq
      obtain ⟨x, y, e', t, htJ, hzt⟩ := hq
      have htI : t ∈ Icc (0 : ℝ) 1 := htJ.1.1
      have hzt' : D.arc e' ⟨t, htI⟩ = D.vertex v := by rw [← Path.extend_apply _ htI, hzt]
      rcases D.arc_avoids_vertices e' ⟨t, htI⟩ v hzt' with rfl | rfl
      · have := ext_inj _ (D.arc_injective e') htI ⟨le_rfl, zero_le_one⟩
          (hzt.trans (D.arc e').extend_zero.symm)
        have := htJ.1.2 rfl
        simp only [mem_Ici] at this
        linarith
      · have := ext_inj _ (D.arc_injective e') htI ⟨zero_le_one, le_rfl⟩
          (hzt.trans (D.arc e').extend_one.symm)
        have := htJ.2 rfl
        simp only [mem_Iic] at this
        linarith
  · rintro z ⟨hzK, hzN⟩
    rw [trace_eq] at hzK
    rcases hzK with ⟨x, rfl⟩ | hz
    · by_cases hx : D.vertex x = D.vertex v
      · exact Or.inl hx
      · exact absurd (Or.inl ⟨⟨x, rfl⟩, hx⟩) hzN
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨x, y, e', t, rfl⟩ := hz
      have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.2
      have hzt : D.arc e' t = (D.arc e').extend t := (Path.extend_extends' _ t).symm
      have htJ : (t : ℝ) ∈ J x y → False := fun hJ => hzN (Or.inr (Set.mem_iUnion.2 ⟨x,
        Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨e', (t : ℝ), hJ, hzt.symm⟩⟩⟩))
      have hxy : x ≠ y := G.ne_of_adj e'
      by_cases hx : x = v
      · subst hx
        by_cases t0 : (t : ℝ) = 0
        · left
          rw [hzt, t0, Path.extend_zero]; rfl
        by_cases tη : (t : ℝ) < η
        · right
          refine Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨e', t, ⟨?_, tη⟩, hzt.symm⟩⟩
          exact lt_of_le_of_ne htI.1 (Ne.symm t0)
        · exact (htJ ⟨⟨htI, fun _ => le_of_not_gt tη⟩, fun hh => absurd hh.symm hxy⟩).elim
      by_cases hy : y = v
      · subst hy
        have hrev : D.arc e' = (D.arc e'.symm).symm := D.arc_reverse e'.symm
        by_cases t1 : (t : ℝ) = 1
        · left
          rw [hzt, t1, Path.extend_one]; rfl
        by_cases tη : 1 - (t : ℝ) < η
        · right
          refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨e'.symm, 1 - t, ⟨?_, tη⟩, ?_⟩⟩
          · have := lt_of_le_of_ne htI.2 t1; linarith
          · rw [hzt, hrev, ext_symm _ htI]
        · exact (htJ ⟨⟨htI, fun hh => absurd hh hx⟩, fun _ => by
            simp only [mem_Iic]; linarith⟩).elim
      · exact (htJ ⟨⟨htI, fun hh => absurd hh hx⟩, fun hh => absurd hh hy⟩).elim

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-! ## The boundary curve -/
theorem cont_slice (h : Hyp D F) : Continuous (F 0) := by
  have : Continuous (fun t : ℝ => ((0 : ℝ), t)) := by fun_prop
  exact h.cont.comp_continuous this (fun t => ⟨le_refl (0 : ℝ), trivial⟩)

theorem psi_mem_trace (h : Hyp D F) (s : ℝ) : F 0 s ∈ D.trace Set.univ := by
  set K := D.trace Set.univ with hK
  set Ω := D.outerFace Set.univ with hΩ
  have hKc : IsClosed K := (trace_compact D).isClosed
  have hmemΩ : ∀ z, z ∈ Ω ↔ z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) :=
    fun z => Iff.rfl
  have hcompΩ : ∀ z ∈ Ω, connectedComponentIn Kᶜ z ⊆ Ω := by
    intro z hz w hw
    have e := connectedComponentIn_eq hw
    rw [hmemΩ] at hz ⊢
    refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
    rw [← e]
    exact hz.2
  have hΩopen : IsOpen Ω := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn Kᶜ z, hcompΩ z hz,
      hKc.isOpen_compl.connectedComponentIn, mem_connectedComponentIn ((hmemΩ z).1 hz).1⟩
  have hfrK : frontier Ω ⊆ K := by
    intro q hq
    by_contra hqK
    rw [hΩopen.frontier_eq] at hq
    obtain ⟨z, hzC, hzΩ⟩ := mem_closure_iff.1 hq.1 (connectedComponentIn Kᶜ q)
      hKc.isOpen_compl.connectedComponentIn (mem_connectedComponentIn hqK)
    apply hq.2
    rw [hmemΩ] at hzΩ ⊢
    refine ⟨hqK, ?_⟩
    rw [connectedComponentIn_eq hzC]
    exact hzΩ.2
  apply hfrK
  rw [← h.bdry]
  exact ⟨s, rfl⟩

/-- Two visits to `p` with a non-`p` point between them can be shrunk to consecutive visits. -/
theorem consecutive (h : Hyp D F) {a b : ℝ} (hab : a < b) {p : Plane} (ha : F 0 a = p)
    (hb : F 0 b = p) :
    ∃ s₁ s₂, a ≤ s₁ ∧ s₁ < s₂ ∧ s₂ ≤ b ∧ F 0 s₁ = p ∧ F 0 s₂ = p ∧
      ∀ s ∈ Ioo s₁ s₂, F 0 s ≠ p := by
  have hcont := cont_slice h
  have hcl : IsClosed (F 0 ⁻¹' {p}) := isClosed_singleton.preimage hcont
  obtain ⟨θ, hθ, hθp⟩ := h.light a b hab
  rw [ha] at hθp
  have hθa : a < θ := lt_of_le_of_ne hθ.1 (by rintro rfl; exact hθp ha)
  have hθb : θ < b := lt_of_le_of_ne hθ.2 (by rintro rfl; exact hθp hb)
  set S1 := Icc a θ ∩ F 0 ⁻¹' {p}
  set S2 := Icc θ b ∩ F 0 ⁻¹' {p}
  have hS1 : IsCompact S1 := isCompact_Icc.inter_right hcl
  have hS2 : IsCompact S2 := isCompact_Icc.inter_right hcl
  have hn1 : S1.Nonempty := ⟨a, ⟨le_rfl, hθa.le⟩, ha⟩
  have hn2 : S2.Nonempty := ⟨b, ⟨hθb.le, le_rfl⟩, hb⟩
  obtain ⟨⟨h1a, h1θ⟩, h1p⟩ := hS1.sSup_mem hn1
  obtain ⟨⟨h2θ, h2b⟩, h2p⟩ := hS2.sInf_mem hn2
  have h1θ' : sSup S1 < θ := lt_of_le_of_ne h1θ (by intro hh; rw [hh] at h1p; exact hθp h1p)
  have h2θ' : θ < sInf S2 := lt_of_le_of_ne h2θ (by intro hh; rw [← hh] at h2p; exact hθp h2p)
  refine ⟨sSup S1, sInf S2, h1a, h1θ'.trans h2θ', h2b, h1p, h2p, ?_⟩
  rintro s ⟨hs1, hs2⟩ hsp
  rcases le_or_gt s θ with hsθ | hsθ
  · have : s ≤ sSup S1 := le_csSup hS1.bddAbove ⟨⟨by linarith, hsθ⟩, hsp⟩
    linarith
  · have : sInf S2 ≤ s := csInf_le hS2.bddBelow ⟨⟨hsθ.le, by linarith⟩, hsp⟩
    linarith

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
/-- Each vertex is visited finitely often in one period. -/
theorem vertex_finite {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) (v : V) (c : ℝ) :
    {t ∈ Set.Ico c (c + 1) | F 0 t = D.vertex v}.Finite := by
  by_contra hinf
  set p := D.vertex v with hp
  set P := {t ∈ Set.Ico c (c + 1) | F 0 t = D.vertex v}
  have hcont := cont_slice h
  obtain ⟨N, hNo, hpN, hKN⟩ := germ_vertex D v (η := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨ts, -, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_Icc (a := c) (b := c + 1)) (fun t ht => Ico_subset_Icc_self ht.1)
  have hcl : IsClosed (F 0 ⁻¹' {p}) := isClosed_singleton.preimage hcont
  have hts : F 0 ts = p := by
    have h1 : ts ∈ closure P := mem_closure_iff_clusterPt.2 hacc.clusterPt
    have h2 : closure P ⊆ F 0 ⁻¹' {p} := closure_minimal (fun t ht => ht.2) hcl
    exact h2 h1
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.1 (hNo.preimage hcont) ts (by
    show F 0 ts ∈ N; rw [hts]; exact hpN)
  set δ := min δ0 (1 / 4) with hδ
  have hδpos : 0 < δ := lt_min hδ0 (by norm_num)
  obtain ⟨s, ⟨hsB, hsP⟩, hsne⟩ := accPt_iff_nhds.1 hacc (Metric.ball ts δ)
    (Metric.ball_mem_nhds _ hδpos)
  have hsts : |s - ts| < δ := by rw [← Real.dist_eq]; exact hsB
  obtain ⟨a, ha_def⟩ : ∃ a, a = min s ts := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = max s ts := ⟨_, rfl⟩
  have hab : a < b := by rw [ha_def, hb_def]; exact min_lt_max.2 hsne
  have hδ1 : δ ≤ δ0 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 4 := min_le_right _ _
  rw [abs_lt] at hsts
  have hFa : F 0 a = p := by
    rcases min_choice s ts with hh | hh <;> rw [ha_def, hh]
    · exact hsP.2
    · exact hts
  have hFb : F 0 b = p := by
    rcases max_choice s ts with hh | hh <;> rw [hb_def, hh]
    · exact hsP.2
    · exact hts
  have ha1 : ts - δ < a ∧ a ≤ ts := by
    rcases min_choice s ts with hh | hh <;> rw [ha_def, hh] <;>
      constructor <;> linarith [min_le_right s ts]
  have hb1 : ts ≤ b ∧ b < ts + δ := by
    rcases max_choice s ts with hh | hh <;> rw [hb_def, hh] <;>
      constructor <;> linarith [le_max_right s ts]
  have hwin : ∀ x ∈ Icc a b, F 0 x ∈ N := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hba : b < a + 1 := by linarith
  obtain ⟨s₁, s₂, has₁, h12, hs₂b, hF1, hF2, hfree⟩ := consecutive h hab hFa hFb
  have h21 : s₂ < s₁ + 1 := by linarith
  set S := F 0 '' Ioo s₁ s₂ with hS
  have hSN : ∀ x ∈ Ioo s₁ s₂, F 0 x ∈ D.trace Set.univ ∩ N := fun x hx =>
    ⟨psi_mem_trace h x, hwin x ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
  have hSgerm : ∀ x ∈ Ioo s₁ s₂, F 0 x ∈
      ⋃ (w : V) (e : G.Adj v w), (D.arc e).extend '' Ioo 0 (1 / 2) := by
    intro x hx
    rcases hKN (hSN x hx) with hh | hh
    · exact absurd hh (hfree x hx)
    · exact hh
  set θ := (s₁ + s₂) / 2
  have hθ : θ ∈ Ioo s₁ s₂ := ⟨by simp only [θ]; linarith, by simp only [θ]; linarith⟩
  obtain ⟨w0, e0, ρ, hρ, hz⟩ : ∃ w0, ∃ e0 : G.Adj v w0, ∃ ρ ∈ Ioo (0 : ℝ) (1 / 2),
      (D.arc e0).extend ρ = F 0 θ := by
    have := hSgerm θ hθ
    simp only [Set.mem_iUnion] at this
    obtain ⟨w0, e0, ρ, hρ, hz⟩ := this
    exact ⟨w0, e0, ρ, hρ, hz⟩
  set g := (D.arc e0).extend with hg
  set C1 := g '' Icc 0 (1 / 2)
  set C2 := ⋃ (w : V) (e : G.Adj v w) (_ : w ≠ w0), (D.arc e).extend '' Icc 0 (1 / 2)
  have hC1c : IsCompact C1 := isCompact_Icc.image (D.arc e0).continuous_extend
  have hC2c : IsClosed C2 := (isCompact_iUnion fun w => isCompact_iUnion fun e =>
    isCompact_iUnion fun _ => isCompact_Icc.image (D.arc e).continuous_extend).isClosed
  have hSpre : IsPreconnected S := isPreconnected_Ioo.image _ hcont.continuousOn
  have hSsub : S ⊆ C1 ∪ C2 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hSgerm x hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨w, e, r, hr, hzr⟩ := this
    by_cases hw : w = w0
    · subst hw
      exact Or.inl ⟨r, Ioo_subset_Icc_self hr, hzr⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨hw,
        r, Ioo_subset_Icc_self hr, hzr⟩⟩⟩)
  have hdisj : S ∩ (C1 ∩ C2) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x, hx, rfl⟩ ⟨r1, hr1, hz1⟩ hz2
    obtain ⟨w, e, hw, r2, hr2, hz2⟩ : ∃ w, ∃ e : G.Adj v w, w ≠ w0 ∧
        ∃ r2 ∈ Icc (0 : ℝ) (1 / 2), (D.arc e).extend r2 = F 0 x := by
      simp only [C2, Set.mem_iUnion] at hz2
      obtain ⟨w, e, hw, r2, hr2, hz2⟩ := hz2
      exact ⟨w, e, hw, r2, hr2, hz2⟩
    have hr1I : r1 ∈ Icc (0 : ℝ) 1 := ⟨hr1.1, by linarith [hr1.2]⟩
    have hr2I : r2 ∈ Icc (0 : ℝ) 1 := ⟨hr2.1, by linarith [hr2.2]⟩
    have heq : D.arc e0 ⟨r1, hr1I⟩ = D.arc e ⟨r2, hr2I⟩ := by
      rw [← Path.extend_apply _ hr1I, ← Path.extend_apply _ hr2I, hz1, hz2]
    rcases D.arcs_meet_only_at_endpoints e0 e _ _ heq with ⟨-, hh⟩ | ⟨hh, -⟩ | ⟨h0 | h1, -⟩
    · exact hw hh.symm
    · exact G.ne_of_adj e hh
    · have hr0 : r1 = 0 := congrArg Subtype.val h0
      apply hfree x hx
      rw [← hz1, hr0]
      exact Path.extend_zero _
    · have hr0 : r1 = 1 := congrArg Subtype.val h1
      linarith [hr1.2]
  have hSC1 : S ⊆ C1 := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hSpre C1 C2 hC1c.isClosed hC2c
      hSsub hdisj with hh | hh
    · exact hh
    · exfalso
      have hzS : F 0 θ ∈ S := ⟨θ, hθ, rfl⟩
      have : F 0 θ ∈ S ∩ (C1 ∩ C2) :=
        ⟨hzS, ⟨ρ, Ioo_subset_Icc_self hρ, hz⟩, hh hzS⟩
      rw [hdisj] at this
      exact this
  have hg0 : g 0 = p := Path.extend_zero _
  have hAc : IsPreconnected C1ᶜ :=
    subarc_compl (D.arc e0) (D.arc_injective e0) le_rfl (by norm_num) (by norm_num)
  have hAK : C1 ⊆ D.trace Set.univ := by
    rintro _ ⟨x, -, rfl⟩; exact ext_mem_trace D e0 x
  have hψA : F 0 '' Icc s₁ s₂ ⊆ C1 := by
    rintro _ ⟨x, hx, rfl⟩
    rcases eq_or_lt_of_le hx.1 with hx1 | hx1
    · rw [← hx1, hF1, ← hg0]; exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
    rcases eq_or_lt_of_le hx.2 with hx2 | hx2
    · rw [hx2, hF2, ← hg0]; exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
    exact hSC1 ⟨x, ⟨hx1, hx2⟩, rfl⟩
  set C := g '' Ioc 0 1
  have hC : IsPreconnected C := isPreconnected_Ioc.image _ (D.arc e0).continuous_extend.continuousOn
  have hCK : C ⊆ D.trace Set.univ \ {F 0 s₁} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨ext_mem_trace D e0 x, ?_⟩
    intro hx'
    rw [Set.mem_singleton_iff, hF1, ← hg0] at hx'
    have := ext_inj _ (D.arc_injective e0) ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_le_one⟩ hx'
    linarith [hx.1]
  have hCm : (C ∩ F 0 '' Ioo s₁ s₂).Nonempty :=
    ⟨F 0 θ, ⟨ρ, ⟨hρ.1, by linarith [hρ.2]⟩, hz⟩, θ, hθ, rfl⟩
  have hsub := no_small_loop h h12 h21 (hF1.trans hF2.symm) C1 hC1c hAK hAc hψA C hC hCK hCm
  obtain ⟨u, hu, hu1⟩ := hsub (⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩ : g 1 ∈ C)
  have := ext_inj _ (D.arc_injective e0) ⟨hu.1, by linarith [hu.2]⟩ ⟨zero_le_one, le_rfl⟩ hu1
  linarith [hu.2]

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias vertex_finite := OuterplanarL1Tan.Dev.FR.PartL.vertex_finite

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartL
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
open Set
/-- Near a visit to the interior of an edge, the boundary curve is injective (no folds). -/
theorem loc_inj {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) {v w : V} (e : G.Adj v w) (σ : unitInterval)
    (hσ0 : 0 < (σ : ℝ)) (hσ1 : (σ : ℝ) < 1) (t : ℝ) (ht : F 0 t = D.arc e σ) :
    ∃ δ > 0, Set.InjOn (F 0) (Set.Ioo (t - δ) (t + δ)) := by
  set g := (D.arc e).extend with hg
  set η := min (σ : ℝ) (1 - σ) / 2 with hηdef
  have hη : 0 < η := by
    have : 0 < min (σ : ℝ) (1 - σ) := lt_min hσ0 (by linarith)
    positivity
  have hη1 : η ≤ (σ : ℝ) / 2 := by
    have := min_le_left (σ : ℝ) (1 - σ); simp only [η]; linarith
  have hη2 : η ≤ (1 - σ) / 2 := by
    have := min_le_right (σ : ℝ) (1 - σ); simp only [η]; linarith
  have hlo : 0 < (σ : ℝ) - η := by linarith
  have hhi : (σ : ℝ) + η < 1 := by linarith
  obtain ⟨N, hNo, hpN, hKN⟩ := germ_edge D e hσ0 hσ1 hη
  have hcont := cont_slice h
  have hgσ : g σ = D.arc e σ := Path.extend_extends' _ σ
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.1 (hNo.preimage hcont) t (by
    show F 0 t ∈ N; rw [ht, ← hgσ]; exact hpN)
  set δ := min δ0 (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ1 : δ ≤ δ0 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  have hU : ∀ s ∈ Ioo (t - δ) (t + δ), F 0 s ∈ g '' Ioo ((σ : ℝ) - η) (σ + η) := by
    intro s hs
    refine hKN ⟨psi_mem_trace h s, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hIcc : ∀ x ∈ Ioo ((σ : ℝ) - η) (σ + η), x ∈ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have key : ∀ s₁ ∈ Ioo (t - δ) (t + δ), ∀ s₂ ∈ Ioo (t - δ) (t + δ), s₁ < s₂ →
      F 0 s₁ ≠ F 0 s₂ := by
    intro s₁ h1 s₂ h2 hlt heq
    have h21 : s₂ < s₁ + 1 := by linarith [h1.1, h2.2]
    set A := g '' Icc ((σ : ℝ) - η) (σ + η)
    have hA : IsCompact A := isCompact_Icc.image (D.arc e).continuous_extend
    have hAK : A ⊆ D.trace Set.univ := by
      rintro _ ⟨x, -, rfl⟩; exact ext_mem_trace D e x
    have hAc : IsPreconnected Aᶜ :=
      subarc_compl (D.arc e) (D.arc_injective e) hlo.le (by linarith) hhi.le
    have hwin : ∀ x ∈ Icc s₁ s₂, x ∈ Ioo (t - δ) (t + δ) := fun x hx =>
      ⟨by linarith [hx.1, h1.1], by linarith [hx.2, h2.2]⟩
    have hψA : F 0 '' Icc s₁ s₂ ⊆ A := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hu'⟩ := hU x (hwin x hx)
      exact ⟨u, Ioo_subset_Icc_self hu, hu'⟩
    obtain ⟨σ', hσ', hy⟩ := hU s₁ h1
    obtain ⟨θ, hθ, hθne⟩ := h.light s₁ s₂ hlt
    have hθ1 : s₁ < θ := lt_of_le_of_ne hθ.1 (by rintro rfl; exact hθne rfl)
    have hθ2 : θ < s₂ := lt_of_le_of_ne hθ.2 (by rintro rfl; exact hθne heq.symm)
    obtain ⟨ρ, hρ, hz⟩ := hU θ (hwin θ hθ)
    have hρne : ρ ≠ σ' := by rintro rfl; exact hθne (hz.symm.trans hy)
    have hσ'I := hIcc σ' hσ'
    have hρI := hIcc ρ hρ
    rcases lt_or_gt_of_ne hρne with hρl | hρg
    · -- `ρ < σ'`
      set C := g '' Ico 0 σ'
      have hC : IsPreconnected C :=
        isPreconnected_Ico.image _ (D.arc e).continuous_extend.continuousOn
      have hCK : C ⊆ D.trace Set.univ \ {F 0 s₁} := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨ext_mem_trace D e x, ?_⟩
        intro hx'
        rw [Set.mem_singleton_iff, ← hy] at hx'
        have := ext_inj _ (D.arc_injective e) ⟨hx.1, by linarith [hx.2, hσ'I.2]⟩ hσ'I hx'
        linarith [hx.2]
      have hCm : (C ∩ F 0 '' Ioo s₁ s₂).Nonempty :=
        ⟨F 0 θ, ⟨ρ, ⟨hρI.1, hρl⟩, hz⟩, θ, ⟨hθ1, hθ2⟩, rfl⟩
      have hsub := no_small_loop h hlt h21 heq A hA hAK hAc hψA C hC hCK hCm
      obtain ⟨u, hu, hu1⟩ := hsub (⟨0, ⟨le_rfl, by linarith [hσ'.1]⟩, rfl⟩ : g 0 ∈ C)
      have := ext_inj _ (D.arc_injective e) ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨le_rfl, zero_le_one⟩ hu1
      linarith [hu.1]
    · -- `σ' < ρ`
      set C := g '' Ioc σ' 1
      have hC : IsPreconnected C :=
        isPreconnected_Ioc.image _ (D.arc e).continuous_extend.continuousOn
      have hCK : C ⊆ D.trace Set.univ \ {F 0 s₁} := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨ext_mem_trace D e x, ?_⟩
        intro hx'
        rw [Set.mem_singleton_iff, ← hy] at hx'
        have := ext_inj _ (D.arc_injective e) ⟨by linarith [hx.1, hσ'I.1], hx.2⟩ hσ'I hx'
        linarith [hx.1]
      have hCm : (C ∩ F 0 '' Ioo s₁ s₂).Nonempty :=
        ⟨F 0 θ, ⟨ρ, ⟨hρg, hρI.2⟩, hz⟩, θ, ⟨hθ1, hθ2⟩, rfl⟩
      have hsub := no_small_loop h hlt h21 heq A hA hAK hAc hψA C hC hCK hCm
      obtain ⟨u, hu, hu1⟩ := hsub (⟨1, ⟨by linarith [hσ'.2], le_rfl⟩, rfl⟩ : g 1 ∈ C)
      have := ext_inj _ (D.arc_injective e) ⟨by linarith [hu.1], by linarith [hu.2]⟩
        ⟨zero_le_one, le_rfl⟩ hu1
      linarith [hu.2]
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (key x hx y hy hlt)
  · exact heq
  · exact absurd hxy.symm (key y hy x hx hgt)

end OuterplanarL1Tan.Dev.FR.PartL
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias loc_inj := OuterplanarL1Tan.Dev.FR.PartL.loc_inj

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartS
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
/-! ## Real-variable lemmas: local injectivity forbids interior extrema -/
/-- A function continuous and injective near an interior point `m` of `[x, y]` has no maximum
on `[x, y]` at `m`. -/
theorem not_isMaxOn_of_injOn {f : ℝ → ℝ} {x y m δ : ℝ} (hm : m ∈ Set.Ioo x y) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc x y))
    (hinj : Set.InjOn f (Set.Ioo (m - δ) (m + δ) ∩ Set.Icc x y))
    (hmax : IsMaxOn f (Set.Icc x y) m) : False := by
  obtain ⟨hxm, hmy⟩ := hm
  set d := min δ (min (m - x) (y - m)) with hd
  have hd0 : 0 < d := lt_min hδ (lt_min (by linarith) (by linarith))
  have hdδ : d ≤ δ := min_le_left _ _
  have hdx : d ≤ m - x := (min_le_right _ _).trans (min_le_left _ _)
  have hdy : d ≤ y - m := (min_le_right _ _).trans (min_le_right _ _)
  set ε := d / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hsub : Set.Icc (m - ε) (m + ε) ⊆ Set.Ioo (m - δ) (m + δ) ∩ Set.Icc x y := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hc' : ContinuousOn f (Set.Icc (m - ε) (m + ε)) :=
    hc.mono (hsub.trans Set.inter_subset_right)
  have hmax' := isMaxOn_iff.1 hmax
  rcases hc'.strictMonoOn_of_injOn_Icc' (by linarith) (hinj.mono hsub) with h | h
  · have h1 := h (a := m) (b := m + ε) ⟨by linarith, by linarith⟩ ⟨by linarith, le_refl _⟩
      (by linarith)
    have h2 := hmax' (m + ε) ⟨by linarith, by linarith⟩
    linarith
  · have h1 := h (a := m - ε) (b := m) ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
    have h2 := hmax' (m - ε) ⟨by linarith, by linarith⟩
    linarith

theorem not_isExtrOn_of_injOn {f : ℝ → ℝ} {x y m δ : ℝ} (hm : m ∈ Set.Ioo x y) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc x y))
    (hinj : Set.InjOn f (Set.Ioo (m - δ) (m + δ) ∩ Set.Icc x y))
    (hext : IsMaxOn f (Set.Icc x y) m ∨ IsMinOn f (Set.Icc x y) m) : False := by
  rcases hext with hmax | hmin
  · exact not_isMaxOn_of_injOn hm hδ hc hinj hmax
  · refine not_isMaxOn_of_injOn (f := fun t => -f t) hm hδ hc.neg ?_ hmin.neg
    intro a ha b hb hab
    exact hinj ha hb (neg_injective hab)

/-- Continuous on `[a, b]` and locally injective at every interior point implies injective. -/
theorem injOn_of_locInj {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Set.Icc a b))
    (hloc : ∀ m ∈ Set.Ioo a b, ∃ δ > 0,
      Set.InjOn f (Set.Ioo (m - δ) (m + δ) ∩ Set.Icc a b)) :
    Set.InjOn f (Set.Icc a b) := by
  have key : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x < y → f x ≠ f y := by
    intro x hx y hy hxy hfe
    have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have hc' := hc.mono hsub
    have hne : (Set.Icc x y).Nonempty := Set.nonempty_Icc.2 hxy.le
    obtain ⟨M, hM, hMmax⟩ := isCompact_Icc.exists_isMaxOn hne hc'
    obtain ⟨n, hn, hnmin⟩ := isCompact_Icc.exists_isMinOn hne hc'
    have interior : ∀ m ∈ Set.Ioo x y,
        IsMaxOn f (Set.Icc x y) m ∨ IsMinOn f (Set.Icc x y) m → False := by
      intro m hm hext
      have hmab : m ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hx.1 hm.1, lt_of_lt_of_le hm.2 hy.2⟩
      obtain ⟨δ, hδ, hinj⟩ := hloc m hmab
      have hinj' : Set.InjOn f (Set.Ioo (m - δ) (m + δ) ∩ Set.Icc x y) :=
        hinj.mono (Set.inter_subset_inter_right _ hsub)
      exact not_isExtrOn_of_injOn hm hδ hc' hinj' hext
    have endpt : ∀ z ∈ Set.Icc x y, z ∉ Set.Ioo x y → f z = f x := by
      intro z hz hz'
      rcases eq_or_lt_of_le hz.1 with h | h
      · rw [h]
      · have : z = y := by
          by_contra hne'
          exact hz' ⟨h, lt_of_le_of_ne hz.2 hne'⟩
        rw [this, hfe]
    by_cases hM' : M ∈ Set.Ioo x y
    · exact interior M hM' (Or.inl hMmax)
    by_cases hn' : n ∈ Set.Ioo x y
    · exact interior n hn' (Or.inr hnmin)
    have hMv := endpt M hM hM'
    have hnv := endpt n hn hn'
    have hmid : (x + y) / 2 ∈ Set.Ioo x y := ⟨by linarith, by linarith⟩
    apply interior _ hmid (Or.inl ?_)
    rw [isMaxOn_iff]
    intro t ht
    have h1 := isMaxOn_iff.1 hMmax t ht
    have h2 := isMinOn_iff.1 hnmin _ (Set.Ioo_subset_Icc_self hmid)
    linarith
  intro x hx y hy hfe
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hfe (key x hx y hy h)
  · exact h
  · exact absurd hfe.symm (key y hy x hx h)

end OuterplanarL1Tan.Dev.FR.PartS
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartS
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
/-! ## Geometry of the drawing -/
theorem trace_eq : D.trace Set.univ =
    Set.range D.vertex ∪ ⋃ (v : V) (w : V) (h : G.Adj v w), Set.range (D.arc h) := by
  ext p
  constructor
  · rintro (⟨⟨v, -⟩, rfl⟩ | hp)
    · exact Or.inl ⟨v, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨v, -⟩, ⟨w, -⟩, h, t, rfl⟩ := hp
      exact Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨h, t, rfl⟩⟩⟩)
  · rintro (⟨v, rfl⟩ | hp)
    · exact Or.inl ⟨⟨v, trivial⟩, rfl⟩
    · simp only [Set.mem_iUnion] at hp
      obtain ⟨v, w, h, t, rfl⟩ := hp
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨⟨v, trivial⟩, ⟨w, trivial⟩, h, t, rfl⟩

theorem arc_closedEmb {v w : V} (e : G.Adj v w) : Topology.IsClosedEmbedding (D.arc e) :=
  (D.arc e).continuous.isClosedEmbedding (D.arc_injective e)

/-- An arc point that is a vertex point is an endpoint. -/
theorem arc_eq_vertex {p q : V} (e : G.Adj p q) (s : unitInterval) (x : V)
    (h : D.arc e s = D.vertex x) :
    (x = p ∧ (s : ℝ) = 0) ∨ (x = q ∧ (s : ℝ) = 1) := by
  rcases D.arc_avoids_vertices e s x h with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have := D.arc_injective e (h.trans (D.arc e).source.symm)
    rw [this]
    rfl
  · right
    refine ⟨rfl, ?_⟩
    have := D.arc_injective e (h.trans (D.arc e).target.symm)
    rw [this]
    rfl

/-- A preconnected part of the drawing avoiding all vertex points lies on a single arc. -/
theorem one_edge [Finite V] {S : Set Plane} (hS : IsPreconnected S)
    (hSK : S ⊆ D.trace Set.univ)
    (hfree : ∀ z ∈ S, ∀ x : V, z ≠ D.vertex x) {z₀ : Plane} (hz₀ : z₀ ∈ S) :
    ∃ p q : V, ∃ e : G.Adj p q, S ⊆ Set.range (D.arc e) := by
  have hz₀K := hSK hz₀
  rw [trace_eq] at hz₀K
  rcases hz₀K with ⟨x, hx⟩ | hz
  · exact absurd hx.symm (hfree z₀ hz₀ x)
  simp only [Set.mem_iUnion] at hz
  obtain ⟨p, q, e, s₀, hs₀⟩ := hz
  refine ⟨p, q, e, ?_⟩
  set A := Set.range (D.arc e) with hAdef
  set B := Set.range D.vertex ∪ ⋃ (v : V) (w : V) (k : G.Adj v w)
    (_ : ¬ ((v = p ∧ w = q) ∨ (v = q ∧ w = p))), Set.range (D.arc k) with hBdef
  have hA : IsClosed A := (isCompact_range (D.arc e).continuous).isClosed
  have hB : IsClosed B :=
    ((Set.finite_range _).isCompact.union (isCompact_iUnion fun v => isCompact_iUnion
      fun w => isCompact_iUnion fun k => isCompact_iUnion
        fun _ => isCompact_range (D.arc k).continuous)).isClosed
  have hcov : S ⊆ A ∪ B := by
    intro z hz
    have hzK := hSK hz
    rw [trace_eq] at hzK
    rcases hzK with hv | hz'
    · exact Or.inr (Or.inl hv)
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨v, w, k, t, rfl⟩ := hz'
    by_cases hvw : (v = p ∧ w = q) ∨ (v = q ∧ w = p)
    · left
      rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨t, rfl⟩
      · refine ⟨unitInterval.symm t, ?_⟩
        have : D.arc k = D.arc e.symm := rfl
        rw [this, D.arc_reverse e, Path.symm_apply]
        rfl
    · right
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨v, w, k, hvw, t, rfl⟩
  have hdisj : S ∩ (A ∩ B) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hz hzA hzB
    obtain ⟨s, rfl⟩ := hzA
    rcases hzB with ⟨x, hx⟩ | hz'
    · exact hfree _ hz x hx.symm
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨v, w, k, hvw, t, ht⟩ := hz'
    rcases D.arcs_meet_only_at_endpoints e k s t ht.symm with h1 | h1 | h1
    · exact hvw (Or.inl ⟨h1.1.symm, h1.2.symm⟩)
    · exact hvw (Or.inr ⟨h1.2.symm, h1.1.symm⟩)
    · rcases h1.1 with h0 | h0
      · apply hfree _ hz p
        rw [h0]
        exact (D.arc e).source
      · apply hfree _ hz q
        rw [h0]
        exact (D.arc e).target
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hS A B hA hB hcov hdisj with h | h
  · exact h
  · exfalso
    have : z₀ ∈ S ∩ (A ∩ B) := ⟨hz₀, ⟨s₀, hs₀⟩, h hz₀⟩
    rw [hdisj] at this
    exact this

/-- A coordinate along an arc for a continuous curve staying on the arc. -/
theorem coord {p q : V} (e : G.Adj p q) {ψ : ℝ → Plane} (hψ : Continuous ψ) {T : Set ℝ}
    (hT : ∀ t ∈ T, ψ t ∈ Set.range (D.arc e)) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ T ∧
      ∀ t ∈ T, ∃ ht : φ t ∈ unitInterval, ψ t = D.arc e ⟨φ t, ht⟩ := by
  classical
  let Φ : T → unitInterval := fun t => Classical.choose (hT t.1 t.2)
  have hΦ : ∀ t : T, D.arc e (Φ t) = ψ t := fun t => Classical.choose_spec (hT t.1 t.2)
  have hΦc : Continuous Φ := by
    rw [(arc_closedEmb D e).isInducing.continuous_iff]
    have : (D.arc e) ∘ Φ = ψ ∘ Subtype.val := funext hΦ
    rw [this]
    exact hψ.comp continuous_subtype_val
  let φ : ℝ → ℝ := fun t => if ht : t ∈ T then (Φ ⟨t, ht⟩ : ℝ) else 0
  have hφ : ∀ t (ht : t ∈ T), φ t = Φ ⟨t, ht⟩ := fun t ht => by simp [φ, ht]
  refine ⟨φ, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : T.domRestrict φ = fun t : T => (Φ t : ℝ) := by
      funext t
      exact hφ t.1 t.2
    rw [this]
    exact continuous_subtype_val.comp hΦc
  · intro t ht
    refine ⟨(hφ t ht) ▸ (Φ ⟨t, ht⟩).2, ?_⟩
    rw [← hΦ ⟨t, ht⟩]
    exact congrArg (D.arc e) (Subtype.ext (hφ t ht).symm)

end OuterplanarL1Tan.Dev.FR.PartS
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartS
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-! ## The boundary curve -/
theorem psi_cont (h : Hyp D F) : Continuous (F 0) := by
  have : Continuous (fun t : ℝ => ((0 : ℝ), t)) := by fun_prop
  exact h.cont.comp_continuous this (fun t => ⟨Set.mem_Ici.2 (le_refl (0 : ℝ)), trivial⟩)

theorem psi_mem (h : Hyp D F) (t : ℝ) : F 0 t ∈ D.trace Set.univ := by
  set K := D.trace Set.univ with hK
  set Ω := D.outerFace Set.univ with hΩ
  have hKc : IsClosed K := by
    rw [hK, trace_eq]
    exact ((Set.finite_range _).isCompact.union (isCompact_iUnion fun v => isCompact_iUnion
      fun w => isCompact_iUnion fun h => isCompact_range (D.arc h).continuous)).isClosed
  have hmemΩ : ∀ z, z ∈ Ω ↔ z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) :=
    fun z => Iff.rfl
  have hcompΩ : ∀ z ∈ Ω, connectedComponentIn Kᶜ z ⊆ Ω := by
    intro z hz w hw
    have e := connectedComponentIn_eq hw
    rw [hmemΩ] at hz ⊢
    refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
    rw [← e]
    exact hz.2
  have hΩopen : IsOpen Ω := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn Kᶜ z, hcompΩ z hz,
      hKc.isOpen_compl.connectedComponentIn, mem_connectedComponentIn ((hmemΩ z).1 hz).1⟩
  have hfrK : frontier Ω ⊆ K := by
    intro q hq
    by_contra hqK
    rw [hΩopen.frontier_eq] at hq
    obtain ⟨z, hzC, hzΩ⟩ := mem_closure_iff.1 hq.1 (connectedComponentIn Kᶜ q)
      hKc.isOpen_compl.connectedComponentIn (mem_connectedComponentIn hqK)
    apply hq.2
    rw [hmemΩ] at hzΩ ⊢
    refine ⟨hqK, ?_⟩
    rw [connectedComponentIn_eq hzC]
    exact hzΩ.2
  apply hfrK
  rw [← h.bdry]
  exact ⟨t, rfl⟩

/-- On a vertex-free stretch running along one arc, the arc coordinate is injective. -/
theorem coord_injOn (h : Hyp D F) {a b : ℝ} {p q : V} (e : G.Adj p q) {φ : ℝ → ℝ}
    (hφc : ContinuousOn φ (Set.Icc a b))
    (hrep : ∀ t ∈ Set.Icc a b, ∃ ht : φ t ∈ unitInterval, F 0 t = D.arc e ⟨φ t, ht⟩)
    (hfree : ∀ t ∈ Set.Ioo a b, ∀ x : V, F 0 t ≠ D.vertex x) :
    Set.InjOn φ (Set.Icc a b) := by
  apply injOn_of_locInj hφc
  intro m hm
  obtain ⟨hmu, hmrep⟩ := hrep m (Set.Ioo_subset_Icc_self hm)
  have h0 : 0 < φ m := by
    rcases eq_or_lt_of_le hmu.1 with h0 | h0
    · exfalso
      apply hfree m hm p
      rw [hmrep]
      refine Eq.trans ?_ (D.arc e).source
      congr 1
      exact Subtype.ext h0.symm
    · exact h0
  have h1 : φ m < 1 := by
    rcases eq_or_lt_of_le hmu.2 with h1 | h1
    · exfalso
      apply hfree m hm q
      rw [hmrep]
      refine Eq.trans ?_ (D.arc e).target
      congr 1
      exact Subtype.ext h1
    · exact h1
  obtain ⟨δ, hδ, hinj⟩ := loc_inj h e ⟨φ m, hmu⟩ h0 h1 m hmrep
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  obtain ⟨hxu, hxrep⟩ := hrep x hx.2
  obtain ⟨hyu, hyrep⟩ := hrep y hy.2
  apply hinj hx.1 hy.1
  rw [hxrep, hyrep]
  exact congrArg (D.arc e) (Subtype.ext hxy)

/-- The boundary curve visits some vertex. -/
theorem exists_vertex {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) : ∃ t : ℝ, ∃ v : V, F 0 t = D.vertex v := by
  by_contra hno
  push Not at hno
  have hψc := psi_cont h
  obtain ⟨p, q, e, hsub⟩ := one_edge D (isPreconnected_range hψc)
    (by rintro _ ⟨t, rfl⟩; exact psi_mem h t)
    (by rintro _ ⟨t, rfl⟩ x; exact hno t x) (Set.mem_range_self 0)
  obtain ⟨φ, hφc, hrep⟩ := coord D e hψc (T := Set.Icc 0 1) (fun t _ => hsub ⟨t, rfl⟩)
  have hinj := coord_injOn h e hφc hrep (fun t _ x => hno t x)
  obtain ⟨h0u, h0rep⟩ := hrep 0 ⟨le_refl _, zero_le_one⟩
  obtain ⟨h1u, h1rep⟩ := hrep 1 ⟨zero_le_one, le_refl _⟩
  have hper : F 0 1 = F 0 0 := by simpa using h.per 0 0
  have : φ 0 = φ 1 := by
    have := D.arc_injective e (h0rep.symm.trans (hper.symm.trans h1rep))
    exact congrArg Subtype.val this
  have := hinj ⟨le_refl _, zero_le_one⟩ ⟨zero_le_one, le_refl _⟩ this
  norm_num at this

end OuterplanarL1Tan.Dev.FR.PartS
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias exists_vertex := OuterplanarL1Tan.Dev.FR.PartS.exists_vertex

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartS
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-- Between two consecutive vertex visits the boundary curve runs once along one edge. -/
theorem segment {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) {a b : ℝ} (hab : a < b) (u w : V)
    (ha : F 0 a = D.vertex u) (hb : F 0 b = D.vertex w)
    (hfree : ∀ t ∈ Set.Ioo a b, ∀ x : V, F 0 t ≠ D.vertex x) :
    ∃ e : G.Adj u w, ∃ g : ℝ → ℝ, ContinuousOn g (Set.Icc a b) ∧
      StrictMonoOn g (Set.Icc a b) ∧ g a = 0 ∧ g b = 1 ∧
      ∀ t ∈ Set.Icc a b, ∀ ht : g t ∈ unitInterval, F 0 t = D.arc e ⟨g t, ht⟩ := by
  have hψc := psi_cont h
  have hmid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨p, q, e, hsub⟩ := one_edge D (isPreconnected_Ioo.image _ hψc.continuousOn)
    (by rintro _ ⟨t, -, rfl⟩; exact psi_mem h t)
    (by rintro _ ⟨t, ht, rfl⟩ x; exact hfree t ht x) (Set.mem_image_of_mem _ hmid)
  have hT : ∀ t ∈ Set.Icc a b, F 0 t ∈ Set.range (D.arc e) := by
    intro t ht
    have hcl : IsClosed (Set.range (D.arc e)) :=
      (isCompact_range (D.arc e).continuous).isClosed
    have h1 : F 0 t ∈ closure (F 0 '' Set.Ioo a b) := by
      apply image_closure_subset_closure_image hψc
      refine ⟨t, ?_, rfl⟩
      rw [closure_Ioo hab.ne]
      exact ht
    exact hcl.closure_subset_iff.2 hsub h1
  obtain ⟨φ, hφc, hrep⟩ := coord D e hψc hT
  have hinj := coord_injOn h e hφc hrep hfree
  have haI : a ∈ Set.Icc a b := ⟨le_refl _, hab.le⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab.le, le_refl _⟩
  obtain ⟨hau, harep⟩ := hrep a haI
  obtain ⟨hbu, hbrep⟩ := hrep b hbI
  have hA := arc_eq_vertex D e _ u (harep.symm.trans ha)
  have hB := arc_eq_vertex D e _ w (hbrep.symm.trans hb)
  simp only at hA hB
  rcases hφc.strictMonoOn_of_injOn_Icc' hab.le hinj with hmono | hanti
  · have hlt := hmono haI hbI hab
    rcases hA with ⟨rfl, hA⟩ | ⟨rfl, hA⟩ <;> rcases hB with ⟨rfl, hB⟩ | ⟨rfl, hB⟩
    · linarith
    · refine ⟨e, φ, hφc, hmono, hA, hB, ?_⟩
      intro t ht ht'
      obtain ⟨_, hr⟩ := hrep t ht
      exact hr
    · linarith
    · linarith
  · have hlt := hanti haI hbI hab
    rcases hA with ⟨rfl, hA⟩ | ⟨rfl, hA⟩ <;> rcases hB with ⟨rfl, hB⟩ | ⟨rfl, hB⟩
    · linarith
    · linarith
    · refine ⟨e.symm, fun t => 1 - φ t, continuousOn_const.sub hφc, ?_, by simp [hA],
        by simp [hB], ?_⟩
      · intro x hx y hy hxy
        have := hanti hx hy hxy
        simp only
        linarith
      · intro t ht ht'
        obtain ⟨_, hr⟩ := hrep t ht
        rw [hr, D.arc_reverse e, Path.symm_apply]
        exact congrArg (D.arc e) (Subtype.ext (by simp [unitInterval.coe_symm_eq]))
    · linarith

end OuterplanarL1Tan.Dev.FR.PartS
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias segment := OuterplanarL1Tan.Dev.FR.PartS.segment

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartS
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
/-- Two disjoint segments of one period never run along the same edge in the same direction. -/
theorem once_cut {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) {a b a' b' : ℝ} (hab : a < b) (hba' : b ≤ a')
    (hab' : a' < b') (hb'a : b' ≤ a + 1) {u w : V} (e : G.Adj u w)
    (g g' : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b)) (hg' : ContinuousOn g' (Set.Icc a' b'))
    (hga : g a = 0) (hgb : g b = 1) (hga' : g' a' = 0) (hgb' : g' b' = 1)
    (hgm : StrictMonoOn g (Set.Icc a b)) (hgm' : StrictMonoOn g' (Set.Icc a' b'))
    (htr : ∀ t ∈ Set.Icc a b, ∀ ht : g t ∈ unitInterval, F 0 t = D.arc e ⟨g t, ht⟩)
    (htr' : ∀ t ∈ Set.Icc a' b', ∀ ht : g' t ∈ unitInterval, F 0 t = D.arc e ⟨g' t, ht⟩) :
    False := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨s₁, hs₁, hgs₁⟩ := intermediate_value_Icc hab.le hg (by rw [hga, hgb]; exact hhalf)
  obtain ⟨s₂, hs₂, hgs₂⟩ := intermediate_value_Icc hab'.le hg' (by rw [hga', hgb']; exact hhalf)
  have hs₁b : s₁ < b := lt_of_le_of_ne hs₁.2 (by rintro rfl; rw [hgb] at hgs₁; norm_num at hgs₁)
  have hs₂b : s₂ < b' :=
    lt_of_le_of_ne hs₂.2 (by rintro rfl; rw [hgb'] at hgs₂; norm_num at hgs₂)
  have hs₁a : a < s₁ :=
    lt_of_le_of_ne hs₁.1 (by rintro rfl; rw [hga] at hgs₁; norm_num at hgs₁)
  have hs₂a : a' < s₂ :=
    lt_of_le_of_ne hs₂.1 (by rintro rfl; rw [hga'] at hgs₂; norm_num at hgs₂)
  have h12 : s₁ < s₂ := by linarith [hs₂.1]
  have h21 : s₂ < s₁ + 1 := by linarith [hs₁.1]
  have hm1 : g s₁ ∈ unitInterval := by rw [hgs₁]; exact hhalf
  have hm2 : g' s₂ ∈ unitInterval := by rw [hgs₂]; exact hhalf
  have hbI : b ∈ Set.Icc a b := ⟨hab.le, le_refl _⟩
  have hb'I : b' ∈ Set.Icc a' b' := ⟨hab'.le, le_refl _⟩
  have hmb : g b ∈ unitInterval := by rw [hgb]; exact ⟨zero_le_one, le_refl _⟩
  have hmb' : g' b' ∈ unitInterval := by rw [hgb']; exact ⟨zero_le_one, le_refl _⟩
  have e1 := htr s₁ hs₁ hm1
  have e2 := htr' s₂ hs₂ hm2
  have eb := htr b hbI hmb
  have eb' := htr' b' hb'I hmb'
  have heq : F 0 s₁ = F 0 s₂ := by
    rw [e1, e2]
    exact congrArg (D.arc e) (Subtype.ext (hgs₁.trans hgs₂.symm))
  have hbb' : F 0 b = F 0 b' := by
    rw [eb, eb']
    exact congrArg (D.arc e) (Subtype.ext (hgb.trans hgb'.symm))
  have hbne : F 0 b ≠ F 0 s₁ := by
    intro hc
    rw [eb, e1] at hc
    have := congrArg Subtype.val (D.arc_injective e hc)
    simp only at this
    rw [hgb, hgs₁] at this
    norm_num at this
  obtain ⟨U, W, -, -, hUW, -, hU, hW⟩ := cut h h12 h21 heq
  have hbU : F 0 b ∈ U := hU ⟨⟨b, ⟨hs₁b, by linarith [hs₂.1]⟩, rfl⟩, hbne⟩
  have hb'W : F 0 b' ∈ W :=
    hW ⟨⟨b', ⟨hs₂b, by linarith [hs₁.1]⟩, rfl⟩, hbb' ▸ hbne⟩
  exact Set.disjoint_left.1 hUW hbU (hbb' ▸ hb'W)

end OuterplanarL1Tan.Dev.FR.PartS
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias once_cut := OuterplanarL1Tan.Dev.FR.PartS.once_cut

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR.PartM
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FR
theorem arc_congr {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) {a b c d : V}
    (h1 : a = c) (h2 : b = d) (e : G.Adj a b) (e' : G.Adj c d) (s : unitInterval) :
    D.arc e s = D.arc e' s := by
  subst h1; subst h2; rfl

theorem sum_ite_range (j : ℕ) (c : ℝ) : ∀ m : ℕ, j < m →
    (∑ i ∈ Finset.range m, (if i < j then (1:ℝ) else if i = j then c else 0)) = j + c := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge j n with hj | hj
    · rw [ih hj]
      have h1 : ¬ n < j := by omega
      have h2 : n ≠ j := by omega
      simp [h1, h2]
    · have hjn : j = n := by omega
      subst hjn
      have : ∀ i ∈ Finset.range j, (if i < j then (1:ℝ) else if i = j then c else 0) = 1 := by
        intro i hi; rw [Finset.mem_range] at hi; simp [hi]
      rw [Finset.sum_congr rfl this]
      simp

theorem sum_ite_fin (m j : ℕ) (c : ℝ) (hj : j < m) :
    (∑ i : Fin m, (if i.val < j then (1:ℝ) else if i.val = j then c else 0)) = j + c :=
  (Fin.sum_univ_eq_sum_range (fun i => if i < j then (1:ℝ) else if i = j then c else 0) m).trans
    (sum_ite_range j c m hj)

theorem assembly {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G}
    {F : ℝ → ℝ → Plane} (h : Hyp D F) :
    ∃ (m : ℕ) (hm : 0 < m) (u : Fin m → V) (τ : ℝ → ℝ),
      Set.range u = D.boundary Set.univ ∧
      (∀ j, G.Adj (u j) (u (cyclicNext hm j))) ∧
      (∀ i j, u i = u j → u (cyclicNext hm i) = u (cyclicNext hm j) → i = j) ∧
      ContinuousOn τ (Set.Icc 0 1) ∧ StrictMonoOn τ (Set.Icc 0 1) ∧ τ 1 = τ 0 + 1 ∧
      ∀ j (e : G.Adj (u j) (u (cyclicNext hm j))) (s : unitInterval),
        F 0 (τ (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) = D.arc e s := by
  classical
  have hper1 : Function.Periodic (F 0) 1 := fun t => h.per 0 t
  obtain ⟨t₀, v₀, hv₀⟩ := exists_vertex h
  obtain ⟨Z, hZdef⟩ : ∃ Z : Set ℝ,
      Z = {t ∈ Set.Ico t₀ (t₀ + 1) | ∃ v, F 0 t = D.vertex v} := ⟨_, rfl⟩
  have hZfin : Z.Finite := by
    have : Z = ⋃ v : V, {t ∈ Set.Ico t₀ (t₀ + 1) | F 0 t = D.vertex v} := by
      ext t; simp [hZdef]
    rw [this]; exact Set.finite_iUnion (fun v => vertex_finite h v t₀)
  have hmemS : ∀ t, t ∈ hZfin.toFinset ↔ t ∈ Z := fun t => Set.Finite.mem_toFinset hZfin
  have ht₀Z : t₀ ∈ Z := by rw [hZdef]; exact ⟨⟨le_rfl, by linarith⟩, v₀, hv₀⟩
  obtain ⟨m, hmdef⟩ : ∃ m, hZfin.toFinset.card = m := ⟨_, rfl⟩
  have hm : 0 < m := by
    rw [← hmdef]; exact Finset.card_pos.mpr ⟨t₀, (hmemS t₀).2 ht₀Z⟩
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ → ℝ, ∀ i, zN i =
      if hi : i < m then hZfin.toFinset.orderEmbOfFin hmdef ⟨i, hi⟩ else t₀ + 1 :=
    ⟨_, fun _ => rfl⟩
  have hzlt : ∀ i (hi : i < m), zN i = hZfin.toFinset.orderEmbOfFin hmdef ⟨i, hi⟩ :=
    fun i hi => by rw [hzN]; simp [hi]
  have hzm : zN m = t₀ + 1 := by rw [hzN]; simp
  have hzZ : ∀ i, i < m → zN i ∈ Z := fun i hi => by
    rw [hzlt i hi, ← hmemS]; exact Finset.orderEmbOfFin_mem _ hmdef _
  have hzIco : ∀ i, i < m → zN i ∈ Set.Ico t₀ (t₀ + 1) := fun i hi => by
    have := hzZ i hi; rw [hZdef] at this; exact this.1
  have hz0 : zN 0 = t₀ := by
    rw [hzlt 0 hm]
    apply le_antisymm
    · rw [Finset.orderEmbOfFin_zero hmdef hm]
      exact Finset.min'_le _ _ ((hmemS t₀).2 ht₀Z)
    · have := hzIco 0 hm; rw [hzlt 0 hm] at this; exact this.1
  have hzmono : StrictMonoOn zN (Set.Iic m) := by
    intro i hi j hj hij
    simp only [Set.mem_Iic] at hi hj
    have him : i < m := lt_of_lt_of_le hij hj
    rcases lt_or_eq_of_le hj with hjm | hjm
    · rw [hzlt i him, hzlt j hjm]
      exact (hZfin.toFinset.orderEmbOfFin hmdef).strictMono (Fin.mk_lt_mk.mpr hij)
    · subst hjm; rw [hzm]; exact (hzIco i him).2
  have hzlt2 : ∀ a b, a < b → b ≤ m → zN a < zN b := fun a b hab hb =>
    hzmono (Set.mem_Iic.2 (hab.le.trans hb)) (Set.mem_Iic.2 hb) hab
  have hzmonoN : ∀ a b, a ≤ b → b ≤ m → zN a ≤ zN b := fun a b hab hb =>
    hzmono.monotoneOn (Set.mem_Iic.2 (hab.trans hb)) (Set.mem_Iic.2 hb) hab
  have hzge : ∀ i, i ≤ m → t₀ ≤ zN i := fun i hi => by
    rw [← hz0]; exact hzmonoN 0 i (Nat.zero_le _) hi
  have hzle : ∀ i, i ≤ m → zN i ≤ t₀ + 1 := fun i hi => by
    rw [← hzm]; exact hzmonoN i m hi le_rfl
  have hzsurj : ∀ t ∈ Z, ∃ k, k < m ∧ zN k = t := by
    intro t ht
    have : t ∈ Set.range (hZfin.toFinset.orderEmbOfFin hmdef) := by
      rw [Finset.range_orderEmbOfFin, Finset.mem_coe]; exact (hmemS t).2 ht
    obtain ⟨⟨k, hk⟩, hk'⟩ := this
    exact ⟨k, hk, by rw [hzlt k hk]; exact hk'⟩
  have hfree : ∀ i, i < m → ∀ t ∈ Set.Ioo (zN i) (zN (i + 1)), ∀ x : V,
      F 0 t ≠ D.vertex x := by
    intro i hi t ht x hx
    have htZ : t ∈ Z := by
      rw [hZdef]
      exact ⟨⟨by linarith [hzge i hi.le, ht.1], by linarith [hzle (i + 1) hi, ht.2]⟩, x, hx⟩
    obtain ⟨k, hk, rfl⟩ := hzsurj t htZ
    have h1 : i < k := (hzmono.lt_iff_lt (Set.mem_Iic.2 hi.le) (Set.mem_Iic.2 hk.le)).1 ht.1
    have h2 : k < i + 1 := (hzmono.lt_iff_lt (Set.mem_Iic.2 hk.le) (Set.mem_Iic.2 hi)).1 ht.2
    omega
  have hex : ∀ j : Fin m, ∃ v, F 0 (zN j) = D.vertex v := fun j => by
    have := hzZ j j.isLt; rw [hZdef] at this; exact this.2
  choose u hu using hex
  have huN : ∀ j : Fin m, F 0 (zN (j.val + 1)) = D.vertex (u (cyclicNext hm j)) := by
    intro j
    by_cases hj : j.val + 1 < m
    · have : cyclicNext hm j = ⟨j.val + 1, hj⟩ :=
        Fin.ext (by simp [cyclicNext, Nat.mod_eq_of_lt hj])
      rw [this, ← hu]
    · have hjm : j.val + 1 = m := by omega
      have : cyclicNext hm j = ⟨0, hm⟩ := Fin.ext (by simp [cyclicNext, hjm])
      rw [this, ← hu, hjm, hzm, hper1 t₀]
      show F 0 t₀ = F 0 (zN 0)
      rw [hz0]
  have hseg : ∀ j : Fin m, ∃ e : G.Adj (u j) (u (cyclicNext hm j)), ∃ g : ℝ → ℝ,
      ContinuousOn g (Set.Icc (zN j) (zN (j.val + 1))) ∧
      StrictMonoOn g (Set.Icc (zN j) (zN (j.val + 1))) ∧
      g (zN j) = 0 ∧ g (zN (j.val + 1)) = 1 ∧
      ∀ t ∈ Set.Icc (zN j) (zN (j.val + 1)), ∀ ht : g t ∈ unitInterval,
        F 0 t = D.arc e ⟨g t, ht⟩ :=
    fun j => segment h (hzlt2 _ _ (Nat.lt_succ_self _) j.isLt) (u j) (u (cyclicNext hm j))
      (hu j) (huN j) (hfree j j.isLt)
  choose e g hgc hgm hg0 hg1 htr using hseg
  -- clamped pieces
  obtain ⟨cl, hcl⟩ : ∃ cl : Fin m → ℝ → ℝ,
      ∀ i t, cl i t = max (zN i) (min t (zN (i.val + 1))) := ⟨_, fun _ _ => rfl⟩
  have hclmem : ∀ (i : Fin m) t, cl i t ∈ Set.Icc (zN i) (zN (i.val + 1)) := fun i t => by
    rw [hcl]
    exact ⟨le_max_left _ _, max_le (hzmonoN _ _ (Nat.le_succ _) i.isLt) (min_le_right _ _)⟩
  have hclcont : ∀ i : Fin m, Continuous (cl i) := fun i => by
    have : cl i = fun t => max (zN i) (min t (zN (i.val + 1))) := funext (hcl i)
    rw [this]; exact continuous_const.max (continuous_id.min continuous_const)
  obtain ⟨corr, hcorr⟩ : ∃ corr : ℝ → ℝ, ∀ t, corr t = t - max t₀ (min t (t₀ + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ → ℝ, ∀ t, Gt t = (∑ i : Fin m, g i (cl i t)) / m + corr t :=
    ⟨_, fun _ => rfl⟩
  have hGc : Continuous Gt := by
    have : Gt = fun t => (∑ i : Fin m, g i (cl i t)) / m + corr t := funext hGt
    rw [this]
    apply Continuous.add
    · apply Continuous.div_const
      apply continuous_finsetSum
      intro i _
      exact (hgc i).comp_continuous (hclcont i) (fun t => hclmem i t)
    · have : corr = fun t => t - max t₀ (min t (t₀ + 1)) := funext hcorr
      rw [this]
      exact continuous_id.sub (continuous_const.max (continuous_id.min continuous_const))
  have hterm_mono : ∀ (i : Fin m) {t t' : ℝ}, t ≤ t' → g i (cl i t) ≤ g i (cl i t') := by
    intro i t t' htt
    apply (hgm i).monotoneOn (hclmem i t) (hclmem i t')
    rw [hcl, hcl]
    exact max_le_max le_rfl (min_le_min htt le_rfl)
  have hcorr_mono : ∀ t t', t ≤ t' → corr t ≤ corr t' := by
    intro t t' htt; rw [hcorr, hcorr]; simp only [max_def, min_def]; split_ifs <;> linarith
  have hpiece : ∀ t, t₀ ≤ t → t < t₀ + 1 → ∃ i : Fin m, zN i ≤ t ∧ t < zN (i.val + 1) := by
    intro t h1 h2
    have hlast : t < zN (m - 1 + 1) := by rw [Nat.sub_add_cancel hm, hzm]; exact h2
    have hP : ∃ k, t < zN (k + 1) := ⟨m - 1, hlast⟩
    obtain ⟨k, hkdef⟩ : ∃ k, Nat.find hP = k := ⟨_, rfl⟩
    have hk : t < zN (k + 1) := hkdef ▸ Nat.find_spec hP
    have hkm : k < m := by
      have := Nat.find_min' hP hlast
      omega
    refine ⟨⟨k, hkm⟩, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · show zN k ≤ t; rw [h0, hz0]; exact h1
    · have := Nat.find_min hP (show k - 1 < Nat.find hP by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  have hGmono : StrictMono Gt := by
    intro t t' htt
    have hS : (∑ i : Fin m, g i (cl i t)) ≤ ∑ i : Fin m, g i (cl i t') :=
      Finset.sum_le_sum (fun i _ => hterm_mono i htt.le)
    have hC := hcorr_mono t t' htt.le
    have key : (∑ i : Fin m, g i (cl i t)) < (∑ i : Fin m, g i (cl i t')) ∨
        corr t < corr t' := by
      by_cases h1 : t < t₀
      · right; rw [hcorr, hcorr]; simp only [max_def, min_def]; split_ifs <;> linarith
      by_cases h2 : t₀ + 1 ≤ t
      · right; rw [hcorr, hcorr]; simp only [max_def, min_def]; split_ifs <;> linarith
      push Not at h1 h2
      left
      obtain ⟨i, hi1, hi2⟩ := hpiece t h1 h2
      apply Finset.sum_lt_sum (fun i _ => hterm_mono i htt.le)
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply hgm i (hclmem i t) (hclmem i t')
      have : cl i t = t := by rw [hcl, min_eq_left hi2.le, max_eq_right hi1]
      rw [this, hcl]
      exact lt_of_lt_of_le (lt_min htt hi2) (le_max_right _ _)
    rw [hGt, hGt]
    rcases key with k | k
    · have := div_lt_div_of_pos_right k hmpos
      linarith
    · have := div_le_div_of_nonneg_right hS hmpos.le
      linarith
  have hGlow : ∀ y, y ≤ 0 → Gt (t₀ + y) = y := by
    intro y hy
    have hsum : (∑ i : Fin m, g i (cl i (t₀ + y))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcl, max_eq_left ((min_le_left _ _).trans (by linarith [hzge i i.isLt.le])), hg0 i]
    rw [hGt, hsum, hcorr, min_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  have hGhigh : ∀ y, 1 ≤ y → Gt (t₀ + y) = y := by
    intro y hy
    have hsum : (∑ i : Fin m, g i (cl i (t₀ + y))) = m := by
      have : ∀ i ∈ (Finset.univ : Finset (Fin m)), g i (cl i (t₀ + y)) = 1 := by
        intro i _
        have h1 : zN (i.val + 1) ≤ t₀ + y := by linarith [hzle (i.val + 1) i.isLt]
        rw [hcl, min_eq_right h1, max_eq_right (hzmonoN _ _ (Nat.le_succ _) i.isLt), hg1 i]
      rw [Finset.sum_congr rfl this]
      simp
    rw [hGt, hsum, hcorr, min_eq_right (by linarith), max_eq_right (by linarith), div_self hm0]
    ring
  have hGsurj : Function.Surjective Gt := by
    intro y
    have ha := hGlow (min y 0) (min_le_right _ _)
    have hb := hGhigh (max y 1) (le_max_right _ _)
    have hab : t₀ + min y 0 ≤ t₀ + max y 1 := by
      linarith [min_le_right y 0, le_max_right y 1]
    have := intermediate_value_Icc hab hGc.continuousOn
    rw [ha, hb] at this
    obtain ⟨t, _, ht⟩ := this ⟨min_le_left _ _, le_max_left _ _⟩
    exact ⟨t, ht⟩
  have hGseg : ∀ (j : Fin m) t, t ∈ Set.Icc (zN j) (zN (j.val + 1)) →
      Gt t = (j.val + g j t) / m := by
    intro j t ht
    have htI1 : t₀ ≤ t := (hzge j j.isLt.le).trans ht.1
    have htI2 : t ≤ t₀ + 1 := ht.2.trans (hzle _ j.isLt)
    have hc0 : corr t = 0 := by
      rw [hcorr, min_eq_left htI2, max_eq_right htI1]; ring
    have hsum : (∑ i : Fin m, g i (cl i t)) = ∑ i : Fin m,
        (if i.val < j.val then (1:ℝ) else if i.val = j.val then g j t else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · rw [if_pos hij]
        have h1 : zN (i.val + 1) ≤ t := (hzmonoN (i.val + 1) j (by omega) j.isLt.le).trans ht.1
        rw [hcl, min_eq_right h1, max_eq_right (hzmonoN _ _ (Nat.le_succ _) i.isLt)]
        exact hg1 i
      · have : i = j := Fin.ext hij
        subst this
        rw [if_neg (lt_irrefl _), if_pos rfl, hcl, min_eq_left ht.2, max_eq_right ht.1]
      · rw [if_neg (by omega), if_neg (by omega)]
        have h1 : t ≤ zN i := ht.2.trans (hzmonoN _ _ (by omega) i.isLt.le)
        rw [hcl, min_eq_left (h1.trans (hzmonoN _ _ (Nat.le_succ _) i.isLt)), max_eq_left h1]
        exact hg0 i
    rw [hGt, hsum, hc0, add_zero, sum_ite_fin m j.val (g j t) j.isLt]
  let eIso := StrictMono.orderIsoOfSurjective Gt hGmono hGsurj
  have hτG : ∀ t, eIso.symm (Gt t) = t := fun t => eIso.symm_apply_apply t
  have hGτ : ∀ x, Gt (eIso.symm x) = x := fun x => eIso.apply_symm_apply x
  have hG0 : Gt t₀ = 0 := by have := hGlow 0 le_rfl; rwa [add_zero] at this
  have hG1 : Gt (t₀ + 1) = 1 := hGhigh 1 le_rfl
  refine ⟨m, hm, u, eIso.symm, ?_, fun j => e j, ?_, eIso.symm.continuous.continuousOn,
    eIso.symm.strictMono.strictMonoOn _, ?_, ?_⟩
  · -- covers_boundary
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨Set.mem_univ _, ?_⟩
      have : D.vertex (u j) ∈ Set.range (F 0) := ⟨zN j, hu j⟩
      rw [h.bdry] at this
      exact frontier_subset_closure this
    · intro hv
      have hnot : D.vertex v ∉ D.outerFace Set.univ := by
        intro hmem
        exact hmem.1 (Or.inl ⟨⟨v, Set.mem_univ v⟩, rfl⟩)
      have hfr : D.vertex v ∈ frontier (D.outerFace Set.univ) :=
        ⟨hv.2, fun hi => hnot (interior_subset hi)⟩
      rw [← h.bdry] at hfr
      obtain ⟨t, ht⟩ := hfr
      have hshift : F 0 (t₀ + Int.fract (t - t₀)) = F 0 t := by
        have : t₀ + Int.fract (t - t₀) = t - (⌊t - t₀⌋ : ℤ) * 1 := by
          rw [Int.fract]; ring
        rw [this, hper1.sub_int_mul_eq]
      have hZ : t₀ + Int.fract (t - t₀) ∈ Z := by
        rw [hZdef]
        refine ⟨⟨by linarith [Int.fract_nonneg (t - t₀)],
          by linarith [Int.fract_lt_one (t - t₀)]⟩, v, ?_⟩
        rw [hshift, ht]
      obtain ⟨k, hk, hk'⟩ := hzsurj _ hZ
      refine ⟨⟨k, hk⟩, D.vertex_injective ?_⟩
      rw [← hu ⟨k, hk⟩, ← ht, ← hshift]
      exact congrArg (F 0) hk'
  · -- once
    have key : ∀ i j : Fin m, i < j → u i = u j →
        u (cyclicNext hm i) = u (cyclicNext hm j) → False := by
      intro i j hij h1 h2
      have hij' : i.val < j.val := hij
      refine once_cut h (a := zN i) (b := zN (i.val + 1)) (a' := zN j) (b' := zN (j.val + 1))
        (hzlt2 _ _ (Nat.lt_succ_self _) i.isLt) (hzmonoN _ _ (by omega) j.isLt.le)
        (hzlt2 _ _ (Nat.lt_succ_self _) j.isLt) ?_ (e i) (g i) (g j) (hgc i) (hgc j)
        (hg0 i) (hg1 i) (hg0 j) (hg1 j) (hgm i) (hgm j) (htr i) ?_
      · linarith [hzle (j.val + 1) j.isLt, hzge i i.isLt.le]
      · intro t ht hg
        rw [htr j t ht hg]
        exact arc_congr D h1.symm h2.symm (e j) (e i) _
    intro i j h1 h2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (key i j hij h1 h2).elim
    · exact hij
    · exact (key j i hij h1.symm h2.symm).elim
  · -- τ 1 = τ 0 + 1
    have a0 : eIso.symm 0 = t₀ := by
      calc eIso.symm 0 = eIso.symm (Gt t₀) := by rw [hG0]
        _ = t₀ := hτG _
    have a1 : eIso.symm 1 = t₀ + 1 := by
      calc eIso.symm 1 = eIso.symm (Gt (t₀ + 1)) := by rw [hG1]
        _ = t₀ + 1 := hτG _
    rw [a0, a1]
  · -- tracing
    intro j e' s
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hlo : Gt (zN j) ≤ ((j.val : ℝ) + (s : ℝ)) / (m : ℝ) := by
      rw [hGseg j (zN j) ⟨le_rfl, (hzlt2 _ _ (Nat.lt_succ_self _) j.isLt).le⟩, hg0 j]
      exact div_le_div_of_nonneg_right (by linarith) hmpos.le
    have hhi : ((j.val : ℝ) + (s : ℝ)) / (m : ℝ) ≤ Gt (zN (j.val + 1)) := by
      rw [hGseg j (zN (j.val + 1)) ⟨(hzlt2 _ _ (Nat.lt_succ_self _) j.isLt).le, le_rfl⟩, hg1 j]
      exact div_le_div_of_nonneg_right (by linarith) hmpos.le
    have hmem : eIso.symm (((j.val : ℝ) + (s : ℝ)) / (m : ℝ)) ∈
        Set.Icc (zN j) (zN (j.val + 1)) := by
      constructor
      · have := eIso.symm.monotone hlo
        rwa [hτG] at this
      · have := eIso.symm.monotone hhi
        rwa [hτG] at this
    have hval := hGseg j _ hmem
    rw [hGτ] at hval
    have hgs : g j (eIso.symm (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) = s := by
      have := ((div_left_inj' hm0).1 hval)
      linarith
    have hgI : g j (eIso.symm (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) ∈ unitInterval := by
      rw [hgs]; exact s.2
    rw [htr j _ hmem hgI]
    have : (⟨_, hgI⟩ : unitInterval) = s := Subtype.ext hgs
    rw [this]

end OuterplanarL1Tan.Dev.FR.PartM
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FR
open OuterplanarL1Tan.Linear
variable {V : Type} [Fintype V] {G : SimpleGraph V} {D : PlaneDrawing G} {F : ℝ → ℝ → Plane}
alias assembly := OuterplanarL1Tan.Dev.FR.PartM.assembly

end OuterplanarL1Tan.Dev.FR
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Linear
theorem chk_exists_facialReparam_of_exteriorParam {V : Type} [Fintype V]
    {G : SimpleGraph V} (connected : G.Connected) (D : PlaneDrawing G)
    (nontrivial : ∃ v w : V, v ≠ w) (F : ℝ → ℝ → Plane)
    (continuous : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ))
    (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    (onto : Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = D.outerFace Set.univ)
    (boundary : Set.range (F 0) = frontier (D.outerFace Set.univ))
    (light : ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β, F 0 θ ≠ F 0 α) :
    ∃ (m : ℕ) (hm : 0 < m) (u : Fin m → V) (τ : ℝ → ℝ),
      Set.range u = D.boundary Set.univ ∧
      (∀ j, G.Adj (u j) (u (cyclicNext hm j))) ∧
      (∀ i j, u i = u j → u (cyclicNext hm i) = u (cyclicNext hm j) → i = j) ∧
      ContinuousOn τ (Set.Icc 0 1) ∧ StrictMonoOn τ (Set.Icc 0 1) ∧ τ 1 = τ 0 + 1 ∧
      ∀ j (h : G.Adj (u j) (u (cyclicNext hm j))) (s : unitInterval),
        F 0 (τ (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) = D.arc h s :=
  OuterplanarL1Tan.Dev.FR.assembly
    ⟨connected, nontrivial, continuous, periodic, injective, onto, boundary, light⟩

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_exists_facialReparam_of_exteriorParam :=
  @OuterplanarL1Tan.Linear.chk_exists_facialReparam_of_exteriorParam
