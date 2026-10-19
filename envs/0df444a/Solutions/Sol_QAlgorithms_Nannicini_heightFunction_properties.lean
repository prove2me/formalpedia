-- Prove2me | solution 1 for QAlgorithms.Nannicini.heightFunction_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T04:05:04.070479+00:00
-- url     : https://prove2.me/submissions/b9cf6bd4-8f2d-47cb-94bb-dd2495300bd3

import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

set_option maxHeartbeats 800000

open QAlgorithms.Nannicini
open scoped RealInnerProductSpace

private lemma lift_combo {m : ℕ} (a b : ℝ) (y z : EuclideanSpace ℝ (Fin m)) (s t : ℝ) :
    liftPoint (a • y + b • z) (a*s+b*t) = a • liftPoint y s + b • liftPoint z t := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftPoint]

private lemma lift_sq {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    ‖liftPoint y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, liftPoint, Fin.sum_univ_castSucc]

private lemma lift_zero {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖liftPoint y 0‖ = ‖y‖ := by
  nlinarith [lift_sq y 0, norm_nonneg (liftPoint y 0), norm_nonneg y]

private lemma lift_inner {m : ℕ} (y z : EuclideanSpace ℝ (Fin m)) (s t : ℝ) :
    inner ℝ (liftPoint y s) (liftPoint z t) = inner ℝ y z + s*t := by
  simp [PiLp.inner_apply, liftPoint, Fin.sum_univ_castSucc, mul_comm]

private lemma lift_surj {m : ℕ} (z : EuclideanSpace ℝ (Fin (m+1))) :
    ∃ y t, z = liftPoint y t := by
  refine ⟨WithLp.toLp 2 (fun i => z i.castSucc), z (Fin.last m), ?_⟩
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftPoint]

private lemma height_le {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {y : EuclideanSpace ℝ (Fin m)} {t : ℝ} (ht : liftPoint y t ∈ K) :
    heightFunction K y ≤ (t : EReal) := sInf_le ⟨t, ht, rfl⟩

private lemma height_lower {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {R : ℝ} (hout : K ⊆ Metric.closedBall 0 R) (y : EuclideanSpace ℝ (Fin m)) :
    ((-R : ℝ) : EReal) ≤ heightFunction K y := by
  apply le_sInf
  rintro _ ⟨t, ht, rfl⟩
  apply EReal.coe_le_coe
  have hn : ‖liftPoint y t‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hout ht
  have ha : |t| ≤ ‖liftPoint y t‖ := by
    nlinarith [lift_sq y t, sq_nonneg ‖y‖, norm_nonneg (liftPoint y t), sq_abs t]
  linarith [neg_abs_le t]

private lemma height_finite {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {R : ℝ} (hout : K ⊆ Metric.closedBall 0 R) {y : EuclideanSpace ℝ (Fin m)}
    (hy : ∃ t, liftPoint y t ∈ K) : heightFunction K y ≠ ⊤ ∧ heightFunction K y ≠ ⊥ := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) (height_le ht),
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (height_lower hout y)⟩

private lemma height_coe {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {R : ℝ} (hout : K ⊆ Metric.closedBall 0 R) {y : EuclideanSpace ℝ (Fin m)}
    (hy : ∃ t, liftPoint y t ∈ K) :
    ((heightFunction K y).toReal : EReal) = heightFunction K y :=
  EReal.coe_toReal (height_finite hout hy).1 (height_finite hout hy).2

private lemma height_approx {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {y : EuclideanSpace ℝ (Fin m)} {t : ℝ} (ht : heightFunction K y < (t : EReal)) :
    ∃ s : ℝ, liftPoint y s ∈ K ∧ s < t := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hst⟩ := (sInf_lt_iff).mp ht
  exact ⟨s, hs, EReal.coe_lt_coe_iff.mp hst⟩

private lemma height_epi {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {R : ℝ} (hout : K ⊆ Metric.closedBall 0 R) (hK : Convex ℝ K) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin m) × ℝ | heightFunction K p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq a b ha hb hab
  change heightFunction K (a • p.1 + b • q.1) ≤ ((a*p.2+b*q.2 : ℝ) : EReal)
  by_cases ha0 : a = 0
  · subst a; have : b = 1 := by linarith
    simpa [this] using hq
  by_cases hb0 : b = 0
  · subst b; have : a = 1 := by linarith
    simpa [this] using hp
  have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hpne : ∃ s, liftPoint p.1 s ∈ K := by
    obtain ⟨s, hs, _⟩ := height_approx (lt_of_le_of_lt hp (EReal.coe_lt_coe (by linarith : p.2 < p.2+1)))
    exact ⟨s, hs⟩
  have hqne : ∃ t, liftPoint q.1 t ∈ K := by
    obtain ⟨t, ht, _⟩ := height_approx (lt_of_le_of_lt hq (EReal.coe_lt_coe (by linarith : q.2 < q.2+1)))
    exact ⟨t, ht⟩
  obtain ⟨s, hs⟩ := hpne
  obtain ⟨t, ht⟩ := hqne
  have hst : liftPoint (a • p.1+b • q.1) (a*s+b*t) ∈ K := by
    rw [lift_combo]; exact hK hs ht ha hb hab
  rw [← height_coe hout ⟨_, hst⟩, EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨s', hs', hs'lt⟩ := height_approx (lt_of_le_of_lt hp (EReal.coe_lt_coe (by linarith : p.2 < p.2+δ)))
  obtain ⟨t', ht', ht'lt⟩ := height_approx (lt_of_le_of_lt hq (EReal.coe_lt_coe (by linarith : q.2 < q.2+δ)))
  have hst' : liftPoint (a • p.1+b • q.1) (a*s'+b*t') ∈ K := by
    rw [lift_combo]; exact hK hs' ht' ha hb hab
  have hh : (heightFunction K (a • p.1+b • q.1)).toReal ≤ a*s'+b*t' := by
    exact EReal.coe_le_coe_iff.mp ((height_coe hout ⟨_, hst⟩).symm ▸ height_le hst')
  nlinarith [mul_le_mul_of_nonneg_left hs'lt.le ha, mul_le_mul_of_nonneg_left ht'lt.le hb]

private lemma fiber_ball {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {r : ℝ} (hin : Metric.closedBall 0 r ⊆ K) {y : EuclideanSpace ℝ (Fin m)}
    (hy : ‖y‖ ≤ r) : liftPoint y 0 ∈ K := by
  apply hin
  simpa [Metric.mem_closedBall, dist_zero_right, lift_zero] using hy

private lemma height_bounds {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {r R : ℝ} (hin : Metric.closedBall 0 r ⊆ K) (hout : K ⊆ Metric.closedBall 0 R)
    {y : EuclideanSpace ℝ (Fin m)} (hy : ‖y‖ ≤ r) :
    -R ≤ (heightFunction K y).toReal ∧ (heightFunction K y).toReal ≤ 0 := by
  have hc := height_coe hout ⟨0, fiber_ball hin hy⟩
  constructor
  · exact EReal.coe_le_coe_iff.mp (hc.symm ▸ height_lower hout y)
  · exact EReal.coe_le_coe_iff.mp (hc.symm ▸ height_le (fiber_ball hin hy))

private lemma height_convex_ball {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {r R : ℝ} (hin : Metric.closedBall 0 r ⊆ K) (hout : K ⊆ Metric.closedBall 0 R)
    (hK : Convex ℝ K) :
    ConvexOn ℝ (Metric.closedBall 0 r) (fun y => (heightFunction K y).toReal) := by
  refine ⟨convex_closedBall _ _, ?_⟩
  intro y hy z hz a b ha hb hab
  have hc : a • y+b • z ∈ Metric.closedBall 0 r := convex_closedBall _ _ hy hz ha hb hab
  have hyco := height_coe hout ⟨0, fiber_ball hin
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)⟩
  have hzco := height_coe hout ⟨0, fiber_ball hin
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)⟩
  have he := height_epi hout hK
    (x := (y, (heightFunction K y).toReal)) (y := (z, (heightFunction K z).toReal))
    hyco.ge hzco.ge ha hb hab
  change heightFunction K (a • y+b • z) ≤ ((a*(heightFunction K y).toReal+b*(heightFunction K z).toReal : ℝ) : EReal) at he
  rw [← height_coe hout ⟨0, fiber_ball hin (by simpa [Metric.mem_closedBall, dist_zero_right] using hc)⟩] at he
  exact EReal.coe_le_coe_iff.mp he

private lemma height_lip {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {r R : ℝ} (hr : 0 < r) (hin : Metric.closedBall 0 r ⊆ K)
    (hout : K ⊆ Metric.closedBall 0 R) (hK : Convex ℝ K)
    {x y : EuclideanSpace ℝ (Fin m)} (hx : ‖x‖ ≤ r/2) (hy : ‖y‖ ≤ r/2) :
    |(heightFunction K x).toReal-(heightFunction K y).toReal| ≤ 2*R/r*dist x y := by
  have oneside {x y : EuclideanSpace ℝ (Fin m)} (hx : ‖x‖ ≤ r/2) (hy : ‖y‖ ≤ r/2) :
      (heightFunction K x).toReal-(heightFunction K y).toReal ≤ 2*R/r*‖x-y‖ := by
    by_cases hxy : x = y
    · subst y; simp
    have hn : 0 < ‖x-y‖ := norm_sub_pos_iff.mpr hxy
    let e := r/2
    have he : 0 < e := by dsimp [e]; positivity
    let z := x + (e/‖x-y‖) • (x-y)
    have hz : ‖z‖ ≤ r := by
      calc
        ‖z‖ ≤ ‖x‖ + ‖(e/‖x-y‖) • (x-y)‖ := norm_add_le _ _
        _ = ‖x‖ + e := by simp [norm_smul, abs_of_pos he, hn.ne']
        _ ≤ r := by dsimp [e]; linarith
    let a := e/(e+‖x-y‖)
    let b := ‖x-y‖/(e+‖x-y‖)
    have hab : a+b=1 := by dsimp [a,b]; field_simp
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hc : a • y+b • z = x := by
      apply PiLp.ext
      intro i
      change a*(y i)+b*(x i+(e/‖x-y‖)*(x i-y i))=x i
      dsimp only [a,b]
      field_simp [hn.ne', ne_of_gt (add_pos he hn)]
      ring
    have hconv := (height_convex_ball hin hout hK).2
      (show y ∈ Metric.closedBall 0 r from by simp only [Metric.mem_closedBall, dist_zero_right]; linarith)
      (show z ∈ Metric.closedBall 0 r from by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
      ha hb hab
    rw [hc] at hconv
    simp only [smul_eq_mul] at hconv
    have hmul : e*((heightFunction K x).toReal-(heightFunction K y).toReal) ≤
        ‖x-y‖*((heightFunction K z).toReal-(heightFunction K x).toReal) := by
      dsimp [a,b] at hconv
      have hh := (le_div_iff₀ (by positivity : 0 < e+‖x-y‖)).mp
        (show (heightFunction K x).toReal ≤
          (e*(heightFunction K y).toReal+‖x-y‖*(heightFunction K z).toReal)/(e+‖x-y‖) by
          simpa only [div_mul_eq_mul_div, ← add_div] using hconv)
      linarith
    have hbx := (height_bounds hin hout (show ‖x‖ ≤ r by linarith)).1
    have hbz := (height_bounds hin hout hz).2
    have hfinal : e*((heightFunction K x).toReal-(heightFunction K y).toReal) ≤ ‖x-y‖*R := by
      nlinarith [mul_nonneg hn.le (show 0 ≤ -(heightFunction K z).toReal by linarith),
        mul_nonneg hn.le (show 0 ≤ (heightFunction K x).toReal+R by linarith)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    dsimp [e] at hfinal
    nlinarith
  rw [abs_sub_le_iff, dist_eq_norm]
  exact ⟨oneside hx hy, by simpa [norm_sub_rev] using oneside hy hx⟩

private lemma height_origin {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m+1)))}
    {r R ε τ : ℝ} (hr : 0 < r) (hR : 0 < R) (hε : 0 < ε) (hτ : 0 < τ)
    (hin : Metric.closedBall 0 r ⊆ K) (hout : K ⊆ Metric.closedBall 0 R) (hK : Convex ℝ K)
    (hx : ¬ Metric.closedBall (liftPoint (0 : EuclideanSpace ℝ (Fin m)) (-τ)) ε ⊆ K) :
    -τ-R*ε/r ≤ (heightFunction K (0 : EuclideanSpace ℝ (Fin m))).toReal := by
  have hco := height_coe hout ⟨0, fiber_ball hin (show ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ r by simpa using hr.le)⟩
  by_contra h
  have hlt : heightFunction K (0 : EuclideanSpace ℝ (Fin m)) < ((-τ-R*ε/r : ℝ) : EReal) := by
    rw [← hco, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨s, hs, hsl⟩ := height_approx hlt
  have hepos : 0 < R*ε/r := by positivity
  have hsneg : s < 0 := by linarith
  have hsτ : τ < -s := by linarith
  have hsR : -s ≤ R := by
    have hn : ‖liftPoint (0 : EuclideanSpace ℝ (Fin m)) s‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hout hs
    have he := lift_sq (0 : EuclideanSpace ℝ (Fin m)) s
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at he
    nlinarith [norm_nonneg (liftPoint (0 : EuclideanSpace ℝ (Fin m)) s)]
  let a := τ/(-s)
  let b := 1-a
  have ha : 0 < a := by dsimp [a]; exact div_pos hτ (neg_pos.mpr hsneg)
  have ha1 : a < 1 := (div_lt_one (by linarith)).mpr hsτ
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a+b=1 := by dsimp [b]; ring
  have hbε : ε ≤ b*r := by
    have hm : R*ε < (-τ-s)*r := by
      have := (div_lt_iff₀ hr).mp (show R*ε/r < -τ-s by linarith)
      nlinarith
    have hbound : (-s)*ε ≤ R*ε := mul_le_mul_of_nonneg_right hsR hε.le
    dsimp [b,a]
    rw [show (1-τ/(-s))*r = ((-s-τ)*r)/(-s) by field_simp [hsneg.ne]; ring,
      le_div_iff₀ (neg_pos.mpr hsneg)]
    nlinarith
  have hcenter : a • liftPoint (0 : EuclideanSpace ℝ (Fin m)) s = liftPoint 0 (-τ) := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [liftPoint, a]; field_simp [hsneg.ne]
    · simp [liftPoint]
  apply hx
  intro z hz
  let v := (1/b) • (z-a • liftPoint (0 : EuclideanSpace ℝ (Fin m)) s)
  have hn : ‖z-a • liftPoint (0 : EuclideanSpace ℝ (Fin m)) s‖ ≤ ε := by
    rw [hcenter]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hv : v ∈ Metric.closedBall 0 r := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1/b)]
    calc
      1/b*‖z-a • liftPoint (0 : EuclideanSpace ℝ (Fin m)) s‖ ≤ 1/b*ε :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ r := by rw [one_div_mul_eq_div, div_le_iff₀ hb]; nlinarith [hbε]
  have hzid : a • liftPoint (0 : EuclideanSpace ℝ (Fin m)) s+b • v = z := by
    dsimp [v]
    rw [smul_smul, mul_one_div_cancel hb.ne', one_smul]
    abel
  rw [← hzid]
  exact hK hs (hin hv) ha.le hb.le hab

theorem solution (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (hK : Convex ℝ K) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hin : Metric.closedBall 0 r ⊆ K) (hout : K ⊆ Metric.closedBall 0 R)
    (ε τ : ℝ) (hε : 0 < ε) (hτ : 0 < τ)
    (hx : ¬ Metric.closedBall (liftPoint 0 (-τ)) ε ⊆ K) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin m) × ℝ | heightFunction K p.1 ≤ (p.2 : EReal)} ∧
    (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
      heightFunction K y ≠ ⊤ ∧ heightFunction K y ≠ ⊥) ∧
    (∀ y₁ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
      ∀ y₂ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r / 2),
        |(heightFunction K y₁).toReal - (heightFunction K y₂).toReal| ≤ 2 * R / r * dist y₁ y₂) ∧
    ∀ (epsBar : ℝ) (g : EuclideanSpace ℝ (Fin m)),
      (∀ y, heightFunction K 0 + ((inner ℝ g y - epsBar : ℝ) : EReal) ≤ heightFunction K y) →
      ∀ z ∈ K, inner ℝ (liftPoint (-g) 1) (liftPoint 0 (-τ)) - (epsBar + R * ε / r) ≤
        inner ℝ (liftPoint (-g) 1) z := by
  classical
  have hR : 0 < R := hr.trans hrR
  have hzero : liftPoint (0 : EuclideanSpace ℝ (Fin m)) 0 ∈ K :=
    fiber_ball hin (by simpa using hr.le)
  refine ⟨height_epi hout hK, ?_, ?_, ?_⟩
  · intro y hy
    exact height_finite hout ⟨0, fiber_ball hin (by
      have hn : ‖y‖ ≤ r/2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
      linarith)⟩
  · intro y hy z hz
    exact height_lip hr hin hout hK
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
  · intro epsBar g hg z hz
    obtain ⟨y,t,rfl⟩ := lift_surj z
    have ht : heightFunction K y ≤ (t : EReal) := height_le hz
    have hh := (hg y).trans ht
    rw [← height_coe hout ⟨0,hzero⟩, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
    have ho := height_origin hr hR hε hτ hin hout hK hx
    rw [lift_inner, lift_inner]
    simp only [inner_zero_right, inner_neg_left, one_mul, zero_add]
    linarith
