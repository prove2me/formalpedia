-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.exists_outerFacialWalk_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:12:51.485637+00:00
-- url     : https://prove2.me/submissions/d10c430e-631e-4864-8cf0-f12b6d5ff260

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry
import Theorems.Thm_ConformalBoundary_caratheodory_torhorst_exterior
import Theorems.Thm_OuterplanarL1Tan_Linear_exists_facialReparam_of_exteriorParam
import Theorems.Thm_JordanCurve_jordan_curve_theorem
import Theorems.Thm_JordanCurve_euclidean_unit_circle_loop

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW
open OuterplanarL1Tan.Linear
/-- Complex numbers as the plane. -/
noncomputable def cx : ℂ ≃ₜ (ℝ × ℝ) := Complex.equivRealProdCLM.toHomeomorph

end OuterplanarL1Tan.Dev.FW
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartG
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW

theorem cx_isBounded_image_iff (A : Set ℂ) :
    Bornology.IsBounded (cx '' A) ↔ Bornology.IsBounded A := by
  constructor
  · intro h
    have h2 := Complex.equivRealProdCLM.symm.lipschitz.isBounded_image h
    have : (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) '' (cx '' A) = A := by
      have e : ∀ a : ℂ, Complex.equivRealProdCLM.symm (cx a) = a :=
        fun a => Complex.equivRealProdCLM.symm_apply_apply a
      rw [Set.image_image]; simp only [e, Set.image_id']
    rwa [this] at h2
  · intro h
    exact Complex.equivRealProdCLM.lipschitz.isBounded_image h

theorem outer_transfer {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) (K : Set ℂ)
    (hK : K = cx ⁻¹' (D.trace Set.univ)) :
    {z | z ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z)} =
      cx ⁻¹' (D.outerFace Set.univ) := by
  subst hK
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, PlaneDrawing.outerFace,
    TaitTobin.Outerplanar.outerFace]
  change _ ↔ cx z ∉ D.trace Set.univ ∧ _
  refine and_congr_right fun hz => not_congr ?_
  have hz' : z ∈ (cx ⁻¹' D.trace Set.univ)ᶜ := hz
  rw [← cx_isBounded_image_iff, cx.image_connectedComponentIn hz', ← Set.preimage_compl,
    cx.image_preimage]
  rfl

end OuterplanarL1Tan.Dev.FW.PartG
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW
open OuterplanarL1Tan.Linear
alias outer_transfer := OuterplanarL1Tan.Dev.FW.PartG.outer_transfer

end OuterplanarL1Tan.Dev.FW
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartG
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
/-- The standard loop `t ↦ exp(2πit)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

theorem ee_def (t : ℝ) : Complex.exp (2 * Real.pi * t * Complex.I) = ee t := rfl

theorem continuous_ee : Continuous ee := by
  unfold ee; fun_prop

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * t * Complex.I) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem ee_add_one (t : ℝ) : ee (t + 1) = ee t := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * ((t + 1 : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * t * Complex.I + 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_one : ee 1 = 1 := by
  have := ee_add_one 0; simpa [ee_zero] using this

theorem ee_inj {t t' : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (ht' : t' ∈ Set.Ico (0 : ℝ) 1)
    (h : ee t = ee t') : t = t' := by
  unfold ee at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have him := congrArg Complex.im hn
  simp at him
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : t = t' + n := by
    have : 2 * Real.pi * t = 2 * Real.pi * (t' + n) := by linarith
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    exact mul_left_cancel₀ h2 this
  have hlt : (n : ℝ) < 1 := by linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hgt : (-1 : ℝ) < n := by linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hn0 : n = 0 := by
    have a : n < 1 := by exact_mod_cast hlt
    have b : -1 < n := by exact_mod_cast hgt
    omega
  subst hn0; simpa using h1

theorem ee_surj {w : ℂ} (hw : ‖w‖ = 1) : ∃ t ∈ Set.Ico (0 : ℝ) 1, ee t = w := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : ∀ t : ℝ, 2 * Real.pi * t = Complex.arg w ∨
      2 * Real.pi * t = Complex.arg w + 2 * Real.pi → ee t = w := by
    intro t ht
    have hw' := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at hw'
    simp only [Complex.ofReal_one, one_mul] at hw'
    rcases ht with ht | ht
    · unfold ee
      have : (2 * (Real.pi : ℂ) * t * Complex.I) = (Complex.arg w : ℂ) * Complex.I := by
        rw [← ht]; push_cast; ring
      rw [this, hw']
    · rw [← hw']; unfold ee
      have : (2 * (Real.pi : ℂ) * t * Complex.I) =
          (Complex.arg w : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by
        have := congrArg (fun x : ℝ => (x : ℂ)) ht
        push_cast at this
        rw [this]; ring
      rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have ha1 := Complex.neg_pi_lt_arg w
  have ha2 := Complex.arg_le_pi w
  by_cases h0 : 0 ≤ Complex.arg w
  · by_cases hp : Complex.arg w = Real.pi
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, key _ (Or.inl ?_)⟩
      rw [hp]; ring
    · refine ⟨Complex.arg w / (2 * Real.pi), ⟨by positivity, ?_⟩, key _ (Or.inl ?_)⟩
      · rw [div_lt_one (by positivity)]
        have := lt_of_le_of_ne ha2 hp
        linarith
      · field_simp
  · push Not at h0
    refine ⟨Complex.arg w / (2 * Real.pi) + 1, ⟨?_, ?_⟩, key _ (Or.inr ?_)⟩
    · have : -(1 / 2 : ℝ) < Complex.arg w / (2 * Real.pi) := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      linarith
    · have : Complex.arg w / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos h0 (by positivity)
      linarith
    · field_simp

theorem norm_polar (r t : ℝ) (hr : 0 ≤ r) : ‖((1 + r : ℝ) : ℂ) * ee t‖ = 1 + r := by
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

theorem polar_cast (r t : ℝ) :
    ((1 + r : ℂ) * Complex.exp (2 * Real.pi * t * Complex.I)) = ((1 + r : ℝ) : ℂ) * ee t := by
  rw [ee_def]; push_cast; ring

theorem polar_surj {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ∃ r t, 0 ≤ r ∧ ((1 + r : ℝ) : ℂ) * ee t = w ∧ r = ‖w‖ - 1 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have h1 : ‖(w / (‖w‖ : ℂ))‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]
  obtain ⟨t, -, ht⟩ := ee_surj h1
  refine ⟨‖w‖ - 1, t, by linarith, ?_, rfl⟩
  rw [ht]
  have : ((1 + (‖w‖ - 1) : ℝ) : ℂ) = (‖w‖ : ℂ) := by push_cast; ring
  rw [this]
  have hn' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem exteriorParam_of_map (Φ : ℂ → ℂ) (U : Set ℂ)
    (hc : ContinuousOn Φ {w | 1 ≤ ‖w‖}) (hi : Set.InjOn Φ {w | 1 < ‖w‖})
    (hU : Φ '' {w | 1 < ‖w‖} = U) (hB : Φ '' Metric.sphere 0 1 = frontier U)
    (hl : ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β,
      Φ (Complex.exp (θ * Complex.I)) ≠ Φ (Complex.exp (α * Complex.I))) :
    let F : ℝ → ℝ → ℝ × ℝ := fun r t =>
      cx (Φ ((1 + r : ℂ) * Complex.exp (2 * Real.pi * t * Complex.I)))
    ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ) ∧
    (∀ r t, F r (t + 1) = F r t) ∧
    Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1) ∧
    Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = cx '' U ∧
    Set.range (F 0) = cx '' frontier U ∧
    (∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β, F 0 θ ≠ F 0 α) := by
  intro F
  have hF : ∀ r t, F r t = cx (Φ (((1 + r : ℝ) : ℂ) * ee t)) := by
    intro r t; simp only [F]; rw [polar_cast]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : Continuous (fun p : ℝ × ℝ => ((1 + p.1 : ℝ) : ℂ) * ee p.2) := by
      have := continuous_ee
      fun_prop
    have heq : Function.uncurry F = fun p : ℝ × ℝ => cx (Φ (((1 + p.1 : ℝ) : ℂ) * ee p.2)) := by
      funext p; exact hF p.1 p.2
    rw [heq]
    refine cx.continuous.comp_continuousOn (hc.comp hg.continuousOn ?_)
    rintro ⟨r, t⟩ ⟨hr, -⟩
    simp only [Set.mem_Ici] at hr
    show 1 ≤ ‖_‖
    rw [norm_polar r t hr]; linarith
  · intro r t; rw [hF, hF, ee_add_one]
  · rintro ⟨r, t⟩ ⟨hr, ht⟩ ⟨r', t'⟩ ⟨hr', ht'⟩ heq
    simp only [Set.mem_Ioi] at hr hr'
    simp only [Function.uncurry_apply_pair, hF] at heq
    have h1 := hi (by show 1 < ‖_‖; rw [norm_polar r t hr.le]; linarith)
      (by show 1 < ‖_‖; rw [norm_polar r' t' hr'.le]; linarith) (cx.injective heq)
    have hrr : r = r' := by
      have := congrArg norm h1
      rw [norm_polar r t hr.le, norm_polar r' t' hr'.le] at this
      linarith
    subst hrr
    have hne : ((1 + r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r : ℝ) ≠ 0)
    have := mul_left_cancel₀ hne h1
    obtain rfl := ee_inj ht ht' this
    rfl
  · ext y
    constructor
    · rintro ⟨⟨r, t⟩, ⟨hr, -⟩, rfl⟩
      simp only [Set.mem_Ioi] at hr
      simp only [Function.uncurry_apply_pair, hF]
      refine ⟨_, ?_, rfl⟩
      rw [← hU]
      refine ⟨_, ?_, rfl⟩
      show 1 < ‖_‖
      rw [norm_polar r t hr.le]; linarith
    · rintro ⟨z, hz, rfl⟩
      rw [← hU] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hw' : 1 < ‖w‖ := hw
      obtain ⟨r, t, -, hrt, hr⟩ := polar_surj hw'.le
      refine ⟨(r, t), ⟨?_, trivial⟩, ?_⟩
      · show 0 < r; rw [hr]; linarith
      · simp only [Function.uncurry_apply_pair, hF, hrt]
  · rw [← hB]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      rw [hF]
      refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm, norm_polar 0 t le_rfl]; norm_num
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hw
      obtain ⟨r, t, -, hrt, hr⟩ := polar_surj hw.ge
      rw [hw, sub_self] at hr
      subst hr
      exact ⟨t, by rw [hF, hrt]⟩
  · intro α β hab
    obtain ⟨θ, hθ, hne⟩ := hl (2 * Real.pi * α) (2 * Real.pi * β) (by
      exact mul_lt_mul_of_pos_left hab (by positivity))
    refine ⟨θ / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ (by positivity)]; linarith [hθ.1]
    · rw [div_le_iff₀ (by positivity)]; linarith [hθ.2]
    · rw [hF, hF]
      intro h
      apply hne
      have h2 := cx.injective h
      have e1 : ((1 + 0 : ℝ) : ℂ) * ee (θ / (2 * Real.pi)) = Complex.exp (θ * Complex.I) := by
        rw [show ((1 + 0 : ℝ) : ℂ) = 1 by norm_num, one_mul]
        unfold ee; congr 1; push_cast; field_simp
      have e2 : ((1 + 0 : ℝ) : ℂ) * ee α = Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
        unfold ee; push_cast; ring_nf
      rw [e1, e2] at h2
      exact h2

theorem trace_eq_of_noAdj {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (v₀ : V) (hv : ∀ v : V, v = v₀) (hno : ∀ a b : V, ¬ G.Adj a b) :
    D.trace Set.univ = {D.vertex v₀} := by
  ext q
  simp only [PlaneDrawing.trace, TaitTobin.Outerplanar.drawingImage, Set.mem_union,
    Set.mem_iUnion, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro (⟨v, rfl⟩ | ⟨a, b, h, -⟩)
    · show D.vertex v.val = _
      rw [hv v.val]
    · exact absurd h (hno _ _)
  · rintro rfl
    exact Or.inl ⟨⟨v₀, trivial⟩, rfl⟩

theorem compl_singleton_unbounded (p : ℝ × ℝ) : ¬ Bornology.IsBounded ({p}ᶜ : Set (ℝ × ℝ)) := by
  intro h
  apply NormedSpace.unbounded_univ ℝ (ℝ × ℝ)
  have := h.union (Bornology.isBounded_singleton (x := p))
  rwa [Set.compl_union_self] at this

theorem outer_eq_of_noAdj {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (v₀ : V) (hv : ∀ v : V, v = v₀) (hno : ∀ a b : V, ¬ G.Adj a b) :
    D.outerFace Set.univ = {D.vertex v₀}ᶜ := by
  have ht := trace_eq_of_noAdj D v₀ hv hno
  show {q | q ∉ D.trace Set.univ ∧
    ¬ Bornology.IsBounded (connectedComponentIn (D.trace Set.univ)ᶜ q)} = _
  rw [ht]
  have hconn : IsConnected ({D.vertex v₀}ᶜ : Set (ℝ × ℝ)) := by
    apply isConnected_compl_singleton_of_one_lt_rank
    rw [rank_prod', Module.rank_self]
    norm_num
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, ?_⟩
    rw [hconn.isPreconnected.connectedComponentIn hq]
    exact compl_singleton_unbounded _

theorem singleton_case {V : Type} [Fintype V] {G : SimpleGraph V} (D : PlaneDrawing G)
    (v₀ : V) (hv : ∀ v : V, v = v₀) : Nonempty (OuterFacialWalk D) := by
  have hno : ∀ a b : V, ¬ G.Adj a b := by
    intro a b h
    rw [hv a, hv b] at h
    exact G.loopless.irrefl _ h
  set p := D.vertex v₀ with hp
  have htr := trace_eq_of_noAdj D v₀ hv hno
  have hout := outer_eq_of_noAdj D v₀ hv hno
  set z₀ : ℂ := cx.symm p with hz₀
  have hcz : cx z₀ = p := cx.apply_symm_apply p
  let c : ℝ → ℝ → ℝ × ℝ := fun r t => cx (z₀ + (r : ℂ) * ee t)
  have hc0 : ∀ t, c 0 t = p := by
    intro t; simp [c, hcz]
  have hnorm : ∀ (r t : ℝ), 0 ≤ r → ‖(r : ℂ) * ee t‖ = r := by
    intro r t hr
    rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hjoint : ∀ (r s t u : ℝ), 0 < r → 0 < s → t ∈ Set.Ico (0 : ℝ) 1 → u ∈ Set.Ico (0 : ℝ) 1 →
      c r t = c s u → r = s ∧ t = u := by
    intro r s t u hr hs ht hu h
    have h1 := add_left_cancel (cx.injective h)
    have hrs : r = s := by
      have := congrArg norm h1
      rwa [hnorm r t hr.le, hnorm s u hs.le] at this
    subst hrs
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact ⟨rfl, ee_inj ht hu (mul_left_cancel₀ hne h1)⟩
  have himg : ∀ r : ℝ, 0 < r → c r '' Set.Icc (0 : ℝ) 1 = cx '' Metric.sphere z₀ r := by
    intro r hr
    ext y
    constructor
    · rintro ⟨t, -, rfl⟩
      refine ⟨_, ?_, rfl⟩
      rw [mem_sphere_iff_norm, add_sub_cancel_left, hnorm r t hr.le]
    · rintro ⟨w, hw, rfl⟩
      rw [mem_sphere_iff_norm] at hw
      have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have h1 : ‖(w - z₀) / (r : ℂ)‖ = 1 := by
        rw [norm_div, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
      obtain ⟨t, ht, het⟩ := ee_surj h1
      refine ⟨t, ⟨ht.1, ht.2.le⟩, ?_⟩
      show cx (z₀ + (r : ℂ) * ee t) = cx w
      rw [het]; congr 1; field_simp; ring
  refine ⟨{
    size := 1
    positive := Nat.one_pos
    vertex := fun _ => v₀
    covers_boundary := ?_
    steps := fun j => Or.inr hv
    once := fun i j _ _ => Subsingleton.elim i j
    collar := c
    exterior := ?_
    traces_edges := fun j h => absurd h (hno _ _)
    traces_singleton := fun j _ t _ => hc0 t }⟩
  · ext v
    simp only [Set.mem_range, PlaneDrawing.boundary, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    rw [hout, closure_compl_singleton]
    exact ⟨fun _ => trivial, fun _ => ⟨0, (hv v).symm⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := continuous_ee
      exact (cx.continuous.comp (by fun_prop)).continuousOn
    · intro r _
      simp only [c, ee_zero, ee_one]
    · intro r hr t ht u hu h
      exact (hjoint r r t u hr.1 hr.1 ht hu h).2
    · intro r hr t _
      rw [hout, Set.mem_compl_singleton_iff]
      intro h
      rw [← hp, ← hcz] at h
      have h1 := cx.injective h
      have h2 : (r : ℂ) * ee t = 0 := by
        have := congrArg (fun x => x - z₀) h1
        simpa using this
      have := congrArg norm h2
      rw [hnorm r t hr.1.le, norm_zero] at this
      exact hr.1.ne' this
    · intro r hr s hs t ht u hu h
      exact hjoint r s t u hr.1 hs.1 ht hu h
    · intro r hr q hq
      rw [htr, Set.mem_singleton_iff] at hq
      subst hq
      rw [himg r hr.1, ← Set.image_compl_eq cx.bijective, ← hp, ← hcz]
      have hmem : z₀ ∈ (Metric.sphere z₀ r)ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_sphere, dist_self]
        exact hr.1.ne
      rw [← cx.image_connectedComponentIn hmem, cx_isBounded_image_iff]
      refine (Metric.isBounded_ball (x := z₀) (r := r)).subset ?_
      refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union
        Metric.isOpen_ball (v := {w | r < dist w z₀})
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)) ?_ ?_
        ⟨z₀, mem_connectedComponentIn hmem, Metric.mem_ball_self hr.1⟩
      · rw [Set.disjoint_left]
        intro w hw hw'
        rw [Metric.mem_ball] at hw
        exact lt_asymm hw hw'
      · intro w hw
        have := connectedComponentIn_subset _ _ hw
        simp only [Set.mem_compl_iff, Metric.mem_sphere] at this
        rcases lt_or_gt_of_ne this with h | h
        · exact Or.inl h
        · exact Or.inr h
    · rw [hout, frontier_compl, frontier, closure_singleton, interior_singleton, Set.sdiff_empty]
      ext y
      simp only [Set.mem_image, Set.mem_singleton_iff, hc0]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, ⟨le_rfl, zero_le_one⟩, h.symm⟩⟩

end OuterplanarL1Tan.Dev.FW.PartG
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW
open OuterplanarL1Tan.Linear
alias singleton_case := OuterplanarL1Tan.Dev.FW.PartG.singleton_case

end OuterplanarL1Tan.Dev.FW
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartG
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
theorem vertex_mem_trace (v : V) : D.vertex v ∈ D.trace Set.univ :=
  Or.inl ⟨⟨v, trivial⟩, rfl⟩

theorem arc_mem_trace {a b : V} (h : G.Adj a b) (t : unitInterval) :
    D.arc h t ∈ D.trace Set.univ := by
  refine Or.inr ?_
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, h, t, rfl⟩

/-- Concatenation of the arcs along a walk. -/
noncomputable def walkPath : {u w : V} → G.Walk u w → Path (D.vertex u) (D.vertex w)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (D.arc h).trans (walkPath p)

theorem range_walkPath_sub {u w : V} (p : G.Walk u w) :
    Set.range (walkPath D p) ⊆ D.trace Set.univ := by
  induction p with
  | nil =>
    rintro _ ⟨t, rfl⟩
    exact vertex_mem_trace D _
  | cons h p ih =>
    show Set.range ((D.arc h).trans (walkPath D p)) ⊆ _
    rw [Path.trans_range]
    refine Set.union_subset ?_ ih
    rintro _ ⟨t, rfl⟩
    exact arc_mem_trace D h t

/-- A loop at `b` running through the arcs of a list of darts. -/
noncomputable def loopPath (b : V) (reach : ∀ v, G.Walk b v) (back : ∀ v, G.Walk v b) :
    List G.Dart → Path (D.vertex b) (D.vertex b)
  | [] => Path.refl _
  | d :: L => ((walkPath D (reach d.toProd.1)).trans
      ((D.arc d.adj).trans (walkPath D (back d.toProd.2)))).trans (loopPath b reach back L)

theorem range_loopPath_sub (b : V) (reach : ∀ v, G.Walk b v) (back : ∀ v, G.Walk v b)
    (L : List G.Dart) : Set.range (loopPath D b reach back L) ⊆ D.trace Set.univ := by
  induction L with
  | nil =>
    rintro _ ⟨t, rfl⟩
    exact vertex_mem_trace D _
  | cons d L ih =>
    show Set.range ((((walkPath D (reach d.toProd.1)).trans
      ((D.arc d.adj).trans (walkPath D (back d.toProd.2)))).trans
        (loopPath D b reach back L))) ⊆ _
    simp only [Path.trans_range]
    refine Set.union_subset (Set.union_subset (range_walkPath_sub D _)
      (Set.union_subset ?_ (range_walkPath_sub D _))) ih
    rintro _ ⟨t, rfl⟩
    exact arc_mem_trace D _ t

theorem arc_sub_loopPath (b : V) (reach : ∀ v, G.Walk b v) (back : ∀ v, G.Walk v b)
    (L : List G.Dart) (d : G.Dart) (hd : d ∈ L) :
    Set.range (D.arc d.adj) ⊆ Set.range (loopPath D b reach back L) := by
  induction L with
  | nil => simp at hd
  | cons e L ih =>
    show _ ⊆ Set.range ((((walkPath D (reach e.toProd.1)).trans
      ((D.arc e.adj).trans (walkPath D (back e.toProd.2)))).trans
        (loopPath D b reach back L)))
    simp only [Path.trans_range]
    rcases List.mem_cons.mp hd with rfl | hd
    · exact fun x hx => Or.inl (Or.inr (Or.inl hx))
    · exact fun x hx => Or.inr (ih hd hx)

end OuterplanarL1Tan.Dev.FW.PartG
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartG
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
theorem trace_curve {V : Type} [Fintype V] {G : SimpleGraph V} (connected : G.Connected)
    (D : PlaneDrawing G) (nontrivial : ∃ v w : V, v ≠ w) :
    ∃ γ : unitInterval → ℂ, Continuous γ ∧ (∃ a b, γ a ≠ γ b) ∧
      Set.range γ = cx ⁻¹' (D.trace Set.univ) := by
  classical
  obtain ⟨v₁, v₂, h12⟩ := nontrivial
  let reach : ∀ v, G.Walk v₁ v := fun v => (connected.preconnected v₁ v).some
  let back : ∀ v, G.Walk v v₁ := fun v => (connected.preconnected v v₁).some
  let L : List G.Dart := (Finset.univ : Finset G.Dart).toList
  let P := loopPath D v₁ reach back L
  have hnb : ∀ v : V, ∃ w, G.Adj v w := by
    intro v
    obtain ⟨u, hu⟩ : ∃ u, u ≠ v := by
      by_cases h : v₁ = v
      · exact ⟨v₂, by rw [← h]; exact h12.symm⟩
      · exact ⟨v₁, h⟩
    obtain ⟨q⟩ := connected.preconnected v u
    cases q with
    | nil => exact absurd rfl hu
    | cons h _ => exact ⟨_, h⟩
  have hrange : Set.range P = D.trace Set.univ := by
    refine (range_loopPath_sub D v₁ reach back L).antisymm ?_
    rintro x (⟨⟨v, -⟩, rfl⟩ | hx)
    · obtain ⟨w, hw⟩ := hnb v
      have := arc_sub_loopPath D v₁ reach back L ⟨(v, w), hw⟩ (by simp [L])
      exact this ⟨0, (D.arc hw).source⟩
    · simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨a, b, h, t, rfl⟩ := hx
      exact arc_sub_loopPath D v₁ reach back L ⟨(a.val, b.val), h⟩ (by simp [L]) ⟨t, rfl⟩
  refine ⟨fun x => cx.symm (P x), cx.symm.continuous.comp P.continuous, ?_, ?_⟩
  · have h1 : D.vertex v₁ ∈ Set.range P := hrange ▸ vertex_mem_trace D v₁
    have h2 : D.vertex v₂ ∈ Set.range P := hrange ▸ vertex_mem_trace D v₂
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    refine ⟨a, b, fun h => h12 (D.vertex_injective ?_)⟩
    rw [← ha, ← hb]
    exact cx.symm.injective h
  · show Set.range (cx.symm ∘ P) = _
    rw [← hrange, Set.range_comp]
    exact congrFun cx.image_symm _

end OuterplanarL1Tan.Dev.FW.PartG
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW
open OuterplanarL1Tan.Linear
alias trace_curve := OuterplanarL1Tan.Dev.FW.PartG.trace_curve

alias exteriorParam_of_map := OuterplanarL1Tan.Dev.FW.PartG.exteriorParam_of_map

end OuterplanarL1Tan.Dev.FW
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartC
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
/-! ## Jordan curves in `ℝ × ℝ` (copied from `PartA`) -/
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
  -- `e`-collisions on `[0,1]`
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

end OuterplanarL1Tan.Dev.FW.PartC
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartC
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
variable {F : ℝ → ℝ → Plane}
/-! ## Periodicity and injectivity -/
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

theorem tau_bounds {τ : ℝ → ℝ} (hτm : StrictMonoOn τ (Set.Icc 0 1)) (hτ1 : τ 1 = τ 0 + 1)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) : τ 0 ≤ τ t ∧ τ t < τ 0 + 1 := by
  refine ⟨hτm.monotoneOn ⟨le_refl 0, zero_le_one⟩ ⟨ht.1, ht.2.le⟩ ht.1, ?_⟩
  rw [← hτ1]
  exact hτm ⟨ht.1, ht.2.le⟩ ⟨zero_le_one, le_refl 1⟩ ht.2

theorem tau_inj {τ : ℝ → ℝ} (hτm : StrictMonoOn τ (Set.Icc 0 1)) (hτ1 : τ 1 = τ 0 + 1)
    {t u : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (h : Int.fract (τ t) = Int.fract (τ u)) : t = u := by
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h
  have b1 := tau_bounds hτm hτ1 ht
  have b2 := tau_bounds hτm hτ1 hu
  have hz0 : z = 0 := by
    have h1 : (z : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < z := by linarith
    have : z < 1 := by exact_mod_cast h1
    have : -1 < z := by exact_mod_cast h2
    omega
  subst hz0
  have : τ t = τ u := by simp only [Int.cast_zero] at hz; linarith
  exact hτm.injOn ⟨ht.1, ht.2.le⟩ ⟨hu.1, hu.2.le⟩ this

theorem collar_inj (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    {τ : ℝ → ℝ} (hτm : StrictMonoOn τ (Set.Icc 0 1)) (hτ1 : τ 1 = τ 0 + 1)
    {r s t u : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (h : F r (τ t) = F s (τ u)) : r = s ∧ t = u := by
  obtain ⟨e1, e2⟩ := inj_fract periodic injective hr hs h
  exact ⟨e1, tau_inj hτm hτ1 ht hu e2⟩

theorem collar_onto (periodic : ∀ r t, F r (t + 1) = F r t) {τ : ℝ → ℝ}
    (hτc : ContinuousOn τ (Set.Icc 0 1)) (hτ1 : τ 1 = τ 0 + 1) (r t : ℝ) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, F r (τ x) = F r t := by
  have hmem : τ 0 + Int.fract (t - τ 0) ∈ Set.Icc (τ 0) (τ 1) := by
    rw [hτ1]
    exact ⟨by linarith [Int.fract_nonneg (t - τ 0)], by linarith [Int.fract_lt_one (t - τ 0)]⟩
  obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc zero_le_one hτc hmem
  refine ⟨x, hx, ?_⟩
  rw [hxe, ← Int.self_sub_floor]
  have : τ 0 + (t - τ 0 - ⌊t - τ 0⌋) = t - ⌊t - τ 0⌋ := by ring
  rw [this]
  exact per_sub_floor periodic r t (t - τ 0)

theorem cont_slice (continuous : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ))
    {r : ℝ} (hr : 0 ≤ r) : Continuous (F r) := by
  have : Continuous (fun t : ℝ => (r, t)) := by fun_prop
  exact continuous.comp_continuous this (fun t => ⟨hr, trivial⟩)

end OuterplanarL1Tan.Dev.FW.PartC
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartC
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
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

/-- Vertex points and arcs of a walk. -/
def wset : {u w : V} → G.Walk u w → Set Plane
  | u, _, .nil => {D.vertex u}
  | _, _, .cons h p => Set.range (D.arc h) ∪ wset p

theorem wset_start {u w : V} (p : G.Walk u w) : D.vertex u ∈ wset D p := by
  cases p with
  | nil => exact rfl
  | cons h p => exact Or.inl ⟨0, (D.arc h).source⟩

theorem wset_end {u w : V} (p : G.Walk u w) : D.vertex w ∈ wset D p := by
  induction p with
  | nil => exact rfl
  | cons h p ih => exact Or.inr ih

theorem wset_pre {u w : V} (p : G.Walk u w) : IsPreconnected (wset D p) := by
  induction p with
  | nil => exact isPreconnected_singleton
  | @cons u v w h p ih =>
    exact IsPreconnected.union (D.vertex v) ⟨1, (D.arc h).target⟩ (wset_start D p)
      (isPreconnected_range (D.arc h).continuous) ih

theorem wset_sub {u w : V} (p : G.Walk u w) : wset D p ⊆
    Set.range D.vertex ∪ ⋃ (v : V) (w : V) (h : G.Adj v w), Set.range (D.arc h) := by
  induction p with
  | nil => intro z hz; exact Or.inl ⟨_, hz.symm⟩
  | cons h p ih =>
    rintro z (⟨t, rfl⟩ | hz)
    · exact Or.inr (Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨h, t, rfl⟩⟩⟩)
    · exact ih hz

theorem trace_preconnected (connected : G.Connected) : IsPreconnected (D.trace Set.univ) := by
  obtain ⟨v0⟩ := connected.nonempty
  rw [trace_eq]
  apply isPreconnected_of_forall (D.vertex v0)
  rintro y (⟨v, rfl⟩ | hy)
  · obtain ⟨p⟩ := connected.preconnected v0 v
    exact ⟨wset D p, wset_sub D p, wset_start D p, wset_end D p, wset_pre D p⟩
  · simp only [Set.mem_iUnion] at hy
    obtain ⟨v, w, h, t, rfl⟩ := hy
    obtain ⟨p⟩ := connected.preconnected v0 v
    refine ⟨wset D p ∪ Set.range (D.arc h), Set.union_subset (wset_sub D p) ?_,
      Or.inl (wset_start D p), Or.inr ⟨t, rfl⟩,
      IsPreconnected.union (D.vertex v) (wset_end D p) ⟨0, (D.arc h).source⟩ (wset_pre D p)
        (isPreconnected_range (D.arc h).continuous)⟩
    rintro _ ⟨s, rfl⟩
    exact Or.inr (Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨h, s, rfl⟩⟩⟩)

end OuterplanarL1Tan.Dev.FW.PartC
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW.PartC
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.FW
/-! ## Enclosure -/
theorem enclosure {V : Type} [Fintype V] {G : SimpleGraph V} (connected : G.Connected)
    (D : PlaneDrawing G) (F : ℝ → ℝ → Plane)
    (continuous : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ))
    (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    (onto : Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = D.outerFace Set.univ)
    (boundary : Set.range (F 0) = frontier (D.outerFace Set.univ))
    (τ : ℝ → ℝ) (hτc : ContinuousOn τ (Set.Icc 0 1)) (hτm : StrictMonoOn τ (Set.Icc 0 1))
    (hτ1 : τ 1 = τ 0 + 1) {r : ℝ} (hr : 0 < r) (p : Plane) (hp : p ∈ D.trace Set.univ) :
    Bornology.IsBounded
      (connectedComponentIn ((fun t => F r (τ t)) '' Set.Icc (0 : ℝ) 1)ᶜ p) := by
  set K := D.trace Set.univ with hK
  set Ω := D.outerFace Set.univ with hΩ
  set J := (fun t => F r (τ t)) '' Set.Icc (0 : ℝ) 1 with hJ
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
  have hJΩ : J ⊆ Ω := by
    rintro _ ⟨t, -, rfl⟩
    rw [← onto]
    exact ⟨(r, τ t), ⟨hr, trivial⟩, rfl⟩
  have hF0 : ∀ t, F 0 t ∈ K := by
    intro t
    apply hfrK
    rw [← boundary]
    exact ⟨t, rfl⟩
  -- the Jordan curve
  have hFr := cont_slice continuous hr.le
  have hτs : Continuous (fun s : unitInterval => τ s) :=
    hτc.comp_continuous continuous_subtype_val (fun s => s.2)
  obtain ⟨g, hgc, hgi, hgr⟩ := circle_param (f := fun s : unitInterval => F r (τ s))
    (hFr.comp hτs) (by show F r (τ 0) = F r (τ 1); rw [hτ1, periodic]) (by
      intro s t hst
      change F r (τ s) = F r (τ t) at hst
      rcases eq_or_lt_of_le s.2.2 with hs1 | hs1 <;>
        rcases eq_or_lt_of_le t.2.2 with ht1 | ht1
      · exact Or.inl (Subtype.ext (hs1.trans ht1.symm))
      · rw [hs1, hτ1, periodic] at hst
        have := (collar_inj periodic injective hτm hτ1 hr hr ⟨le_refl 0, zero_lt_one⟩
          ⟨t.2.1, ht1⟩ hst).2
        exact Or.inr (Or.inr ⟨hs1, this.symm⟩)
      · rw [ht1, hτ1, periodic] at hst
        have := (collar_inj periodic injective hτm hτ1 hr hr ⟨s.2.1, hs1⟩
          ⟨le_refl 0, zero_lt_one⟩ hst).2
        exact Or.inr (Or.inl ⟨this, ht1⟩)
      · exact Or.inl (Subtype.ext (collar_inj periodic injective hτm hτ1 hr hr ⟨s.2.1, hs1⟩
          ⟨t.2.1, ht1⟩ hst).2))
  have hrf : Set.range (fun s : unitInterval => F r (τ s)) = J := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s, s.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  rw [hrf] at hgr
  let φ : ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) := planeHomeo.symm
  obtain ⟨I, O, hIo, hOo, -, -, hIb, -, hdisj, hun, hfI, -⟩ :=
    JordanCurve.jordan_curve_theorem (φ ∘ g) (φ.continuous.comp hgc)
      (φ.injective.comp hgi)
  have hrange : φ ⁻¹' Set.range (φ ∘ g) = J := by
    rw [Set.range_comp, Set.preimage_image_eq _ φ.injective, hgr]
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
  have hI'b : Bornology.IsBounded I' := by
    have e : I' = planeHomeo '' I := congrFun (Homeomorph.preimage_symm planeHomeo) I
    rw [e]
    exact (hIb.isCompact_closure.image planeHomeo.continuous).isBounded.subset
      (Set.image_mono subset_closure)
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
  -- the two annuli
  have hFrJ : ∀ t, F r t ∈ J := by
    intro t
    obtain ⟨x, hx, he⟩ := collar_onto periodic hτc hτ1 r t
    exact ⟨x, hx, he⟩
  have hJchar : ∀ s t, 0 < s → F s t ∈ J → s = r := by
    rintro s t hs ⟨x, -, he⟩
    exact (inj_fract periodic injective hr hs he).1.symm
  set P := Function.uncurry F '' (Set.Ico 0 r ×ˢ Set.univ) with hP
  set Q := Function.uncurry F '' (Set.Ioi r ×ˢ Set.univ) with hQ
  have hPpre : IsPreconnected P :=
    (isPreconnected_Ico.prod isPreconnected_univ).image _
      (continuous.mono (Set.prod_mono Set.Ico_subset_Ici_self subset_rfl))
  have hQpre : IsPreconnected Q :=
    (isPreconnected_Ioi.prod isPreconnected_univ).image _
      (continuous.mono (Set.prod_mono (fun x (hx : r < x) => le_of_lt (hr.trans hx))
        subset_rfl))
  have hPJ : P ⊆ I' ∪ O' := by
    rw [hun']
    rintro _ ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩ hJs
    change F s t ∈ J at hJs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      exact (hJΩ hJs).1 (hF0 t)
    · have := hJchar s t hpos hJs
      exact lt_irrefl _ (this ▸ hs.2)
  have hQJ : Q ⊆ I' ∪ O' := by
    rw [hun']
    rintro _ ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩ hJs
    change F s t ∈ J at hJs
    have hs' : r < s := hs
    have := hJchar s t (hr.trans hs') hJs
    exact lt_irrefl _ (this ▸ hs')
  -- Ω is unbounded
  have hΩunb : ¬ Bornology.IsBounded Ω := by
    have hz0 : F 1 0 ∈ Ω := by
      rw [← onto]; exact ⟨(1, 0), ⟨by show (0 : ℝ) < 1; norm_num, trivial⟩, rfl⟩
    intro hb
    exact ((hmemΩ _).1 hz0).2 (hb.subset (hcompΩ _ hz0))
  have hΩsub : Ω ⊆ Function.uncurry F '' (Set.Icc 0 r ×ˢ Set.Icc 0 1) ∪ Q := by
    intro z hz
    rw [← onto] at hz
    obtain ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩ := hz
    have hs' : 0 < s := hs
    rcases le_or_gt s r with h | h
    · exact Or.inl ⟨(s, Int.fract t), ⟨⟨hs'.le, h⟩, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩,
        (per_fract periodic s t).symm⟩
    · exact Or.inr ⟨(s, t), ⟨h, trivial⟩, rfl⟩
  have hBc : IsCompact (Function.uncurry F '' (Set.Icc 0 r ×ˢ Set.Icc 0 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (continuous.mono (Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)))
  have hQO : Q ⊆ O' := by
    rcases hQpre.subset_or_subset hI'o hO'o hdisj' hQJ with h | h
    · exact absurd ((hBc.isBounded.union (hI'b.subset h)).subset hΩsub) hΩunb
    · exact h
  have hPI : P ⊆ I' := by
    rcases hPpre.subset_or_subset hI'o hO'o hdisj' hPJ with h | h
    · exact h
    · exfalso
      have hx : F r (τ 0) ∈ J := ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩
      obtain ⟨y, hyΩ, hyI⟩ := mem_closure_iff.1 (hJcl hx) Ω hΩopen (hJΩ hx)
      have hyJ := hI'J y hyI
      rw [← onto] at hyΩ
      obtain ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩ := hyΩ
      have hs' : 0 < s := hs
      rcases lt_trichotomy s r with h1 | h1 | h1
      · exact Set.disjoint_left.1 hdisj' hyI (h ⟨(s, t), ⟨⟨hs'.le, h1⟩, trivial⟩, rfl⟩)
      · subst h1
        exact hyJ (hFrJ t)
      · exact Set.disjoint_left.1 hdisj' hyI (hQO ⟨(s, t), ⟨h1, trivial⟩, rfl⟩)
  have hq0I : F 0 0 ∈ I' := hPI ⟨(0, 0), ⟨⟨le_refl 0, hr⟩, trivial⟩, rfl⟩
  have hKJ : K ⊆ I' ∪ O' := by
    intro z hz
    rw [hun']
    intro hzJ
    exact (hJΩ hzJ).1 hz
  have hKI : K ⊆ I' := by
    rcases (trace_preconnected D connected).subset_or_subset hI'o hO'o hdisj' hKJ with h | h
    · exact h
    · exact absurd (h (hF0 0)) (Set.disjoint_left.1 hdisj' hq0I)
  have hpJ : p ∉ J := fun h => (hJΩ h).1 hp
  have hCsub : connectedComponentIn Jᶜ p ⊆ I' ∪ O' := by
    rw [hun']; exact connectedComponentIn_subset _ _
  rcases isPreconnected_connectedComponentIn.subset_or_subset hI'o hO'o hdisj' hCsub with h | h
  · exact hI'b.subset h
  · exact absurd (h (mem_connectedComponentIn hpJ)) (Set.disjoint_left.1 hdisj' (hKI hp))

/-! ## The stub -/
/-- The collar `c r t = F r (τ t)` makes the reparametrised walk an outer facial walk. -/
theorem collar_of_reparam {V : Type} [Fintype V] {G : SimpleGraph V} (connected : G.Connected)
    (D : PlaneDrawing G) (F : ℝ → ℝ → Plane)
    (continuous : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ))
    (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    (onto : Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = D.outerFace Set.univ)
    (boundary : Set.range (F 0) = frontier (D.outerFace Set.univ))
    (m : ℕ) (hm : 0 < m) (u : Fin m → V) (τ : ℝ → ℝ)
    (hcov : Set.range u = D.boundary Set.univ)
    (hadj : ∀ j, G.Adj (u j) (u (cyclicNext hm j)))
    (honce : ∀ i j, u i = u j → u (cyclicNext hm i) = u (cyclicNext hm j) → i = j)
    (hτc : ContinuousOn τ (Set.Icc 0 1)) (hτm : StrictMonoOn τ (Set.Icc 0 1))
    (hτ1 : τ 1 = τ 0 + 1)
    (htr : ∀ j (h : G.Adj (u j) (u (cyclicNext hm j))) (s : unitInterval),
        F 0 (τ (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) = D.arc h s) :
    Nonempty (OuterFacialWalk D) := by
  refine ⟨⟨m, hm, u, hcov, fun j => Or.inl (hadj j), honce, fun r t => F r (τ t), ?_,
    fun j h s => htr j h s, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Set.Icc_prod_Icc]
      have hin : ContinuousOn (fun q : ℝ × ℝ => (q.1, τ q.2))
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
        continuousOn_fst.prodMk (hτc.comp continuousOn_snd (fun q hq => hq.2))
      exact continuous.comp hin (fun q hq => ⟨hq.1.1, trivial⟩)
    · intro r _
      show F r (τ 0) = F r (τ 1)
      rw [hτ1, periodic]
    · intro r hr t ht s hs h
      exact (collar_inj periodic injective hτm hτ1 hr.1 hr.1 ht hs h).2
    · intro r hr t _
      show F r (τ t) ∈ _
      rw [← onto]
      exact ⟨(r, τ t), ⟨hr.1, trivial⟩, rfl⟩
    · intro r hr s hs t ht u hu h
      exact collar_inj periodic injective hτm hτ1 hr.1 hs.1 ht hu h
    · intro r hr p hp
      exact enclosure connected D F continuous periodic injective onto boundary τ hτc hτm hτ1
        hr.1 p hp
    · rw [← boundary]
      ext z
      constructor
      · rintro ⟨t, -, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨t, rfl⟩
        obtain ⟨x, hx, he⟩ := collar_onto periodic hτc hτ1 0 t
        exact ⟨x, hx, he⟩
  · intro j hj
    exfalso
    have h := hadj j
    rw [hj (u (cyclicNext hm j))] at h
    exact h.ne rfl

end OuterplanarL1Tan.Dev.FW.PartC
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.FW
open OuterplanarL1Tan.Linear
alias collar_of_reparam := OuterplanarL1Tan.Dev.FW.PartC.collar_of_reparam

theorem exists_outerFacialWalk_dev {V : Type} [Fintype V]
    {G : SimpleGraph V} (connected : G.Connected) (D : PlaneDrawing G) :
    Nonempty (OuterFacialWalk D) := by
  by_cases hnt : ∃ v w : V, v ≠ w
  · obtain ⟨γ, hγ, hnd, hK⟩ := trace_curve connected D hnt
    obtain ⟨Φ, hc, -, hi, hU, hB, hl⟩ :=
      ConformalBoundary.caratheodory_torhorst_exterior γ hγ hnd
    have hT := outer_transfer D (Set.range γ) hK
    rw [hT] at hU hB
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exteriorParam_of_map Φ _ hc hi hU hB hl
    have himg : cx '' (cx ⁻¹' (D.outerFace Set.univ)) = D.outerFace Set.univ :=
      Set.image_preimage_eq _ cx.surjective
    have hfr : cx '' frontier (cx ⁻¹' (D.outerFace Set.univ)) =
        frontier (D.outerFace Set.univ) := by
      rw [← cx.preimage_frontier, Set.image_preimage_eq _ cx.surjective]
    rw [himg] at h4
    rw [hfr] at h5
    obtain ⟨m, hm, u, τ, hcov, hadj, honce, hτc, hτm, hτ1, htr⟩ :=
      exists_facialReparam_of_exteriorParam connected D hnt _ h1 h2 h3 h4 h5 h6
    exact collar_of_reparam connected D _ h1 h2 h3 h4 h5 m hm u τ hcov hadj honce hτc hτm hτ1 htr
  · push_neg at hnt
    obtain ⟨v₀⟩ := connected.nonempty
    exact singleton_case D v₀ (fun v => hnt v v₀)

end OuterplanarL1Tan.Dev.FW
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Linear
theorem chk_exists_outerFacialWalk_of_connected {V : Type} [Fintype V]
    {G : SimpleGraph V} (connected : G.Connected) (D : PlaneDrawing G) :
    Nonempty (OuterFacialWalk D) :=
  OuterplanarL1Tan.Dev.FW.exists_outerFacialWalk_dev connected D

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_exists_outerFacialWalk_of_connected :=
  @OuterplanarL1Tan.Linear.chk_exists_outerFacialWalk_of_connected
