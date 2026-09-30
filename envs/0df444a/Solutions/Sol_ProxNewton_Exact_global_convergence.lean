-- Prove2me | solution 1 for ProxNewton.Exact.global_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:24:08.774984+00:00
-- url     : https://prove2.me/submissions/3915be8c-0627-4fa1-9075-3a595ff88d9c

import Definitions.Def_ProxNewton_Exact_Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
open scoped BigOperators RealInnerProductSpace
open Filter Topology ProxNewton.Exact
namespace PNProof
private lemma descent_coarse {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hg : Differentiable ℝ g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    g (x+d) ≤ g x+⟪gradient g x,d⟫+L*‖d‖^2 := by
  let f : ℝ → ℝ := fun t => g (x+t • d)-t*⟪gradient g x,d⟫
  have hd (t : ℝ) : HasDerivAt f ⟪gradient g (x+t • d)-gradient g x,d⟫ t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh := (hg (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    rw [← inner_gradient_left] at hh
    convert! hh.sub ((hasDerivAt_id t).mul_const ⟪gradient g x,d⟫) using 1 <;> simp [f,inner_sub_left]
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖⟪gradient g (x+t • d)-gradient g x,d⟫‖ ≤ L*‖d‖^2 := by
    have hh := hlip (x+t • d) x
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
    calc
      ‖⟪gradient g (x+t • d)-gradient g x,d⟫‖ ≤ ‖gradient g (x+t • d)-gradient g x‖*‖d‖ := norm_inner_le_norm _ _
      _ ≤ (L*(t*‖d‖))*‖d‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = t*(L*‖d‖^2) := by ring
      _ ≤ 1*(L*‖d‖^2) := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hL (sq_nonneg _))
      _ = L*‖d‖^2 := one_mul _
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t ht => (hd t).hasDerivWithinAt) (fun t ht => hb t ⟨ht.1,ht.2.le⟩)
  have hf := le_trans (le_abs_self (f 1-f 0)) hh
  dsimp [f] at hf
  simp only [one_smul,zero_smul,add_zero,one_mul,zero_mul,sub_zero] at hf
  linarith
private lemma convex_step {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hc : ConvexOn ℝ D h)
    (x d : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) (hxd : x+d ∈ D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x+t • d ∈ D ∧ h (x+t • d) ≤ (1-t)*h x+t*h (x+d) := by
  have he : (1-t) • x+t • (x+d) = x+t • d := by module
  exact ⟨he ▸ hc.1 hx hxd (by linarith) ht0 (by ring),
    by simpa only [he,smul_eq_mul] using hc.2 hx hxd (by linarith : 0 ≤ 1-t) ht0 (by ring : 1-t+t=1)⟩
private lemma weak_pred {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (m : ℝ) (hx : x ∈ D)
    (hb : ∀ v, m*‖v‖^2 ≤ ⟪H v,v⟫) (hd : IsSearchDirection g D h x H d) :
    predDecrease g h x d ≤ -(m/2)*‖d‖^2 := by
  have hh := hd.2 0 (by simpa using hx)
  simp only [inner_zero_right,map_zero,inner_zero_left,zero_mul,add_zero] at hh
  have := hb d
  dsimp [predDecrease]
  linarith
private lemma short_descent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L m α : ℝ)
    (hg : Differentiable ℝ g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (hc : ConvexOn ℝ D h)
    (hm : 0 < m) (ha : α < 1)
    (x : EuclideanSpace ℝ (Fin n)) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D)
    (hb : ∀ v, m*‖v‖^2 ≤ ⟪H v,v⟫) (hd : IsSearchDirection g D h x H d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (htL : L*t ≤ m/2*(1-α)) :
    SufficientDescent g D h α x d t := by
  have hh := convex_step D h hc x d hx hd.1 t ht0.le ht1
  have hg' := descent_coarse g L hg hL hlip x (t • d)
  simp only [inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,mul_pow] at hg'
  have hp := weak_pred g D h x H d m hx hb hd
  have hs : g (x+t • d)+h (x+t • d) ≤ g x+h x+α*t*predDecrease g h x d := by
    have hq := mul_le_mul_of_nonneg_right htL (sq_nonneg ‖d‖)
    have hr := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-α by linarith)
    have he : (1-α)*predDecrease g h x d+L*t*‖d‖^2 ≤ 0 := by nlinarith
    have he' := mul_nonpos_of_nonneg_of_nonpos ht0.le he
    dsimp [predDecrease] at *
    nlinarith
  simpa only [SufficientDescent,compositeObj,if_pos hh.1,EReal.coe_le_coe_iff] using hs
private lemma descent_domain {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ) (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : SufficientDescent g D h α x d t) : x+t • d ∈ D := by
  classical
  by_contra hn
  dsimp only [SufficientDescent,compositeObj] at ht
  rw [if_neg hn] at ht
  exact (EReal.coe_ne_top _ (top_le_iff.mp ht))
private lemma strong_chord {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hsc : StronglyConvexWith g m) (x y : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g ((1-t) • x+t • y) ≤ (1-t)*g x+t*g y - m/2*t*(1-t)*‖x-y‖^2 := by
  let z := (1-t) • x+t • y
  have h1 := mul_le_mul_of_nonneg_left (hsc z x) (show 0 ≤ 1-t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hsc z y) ht0
  have hzx : z-x = -t • (x-y) := by dsimp [z]; module
  have hzy : z-y = (1-t) • (x-y) := by dsimp [z]; module
  have hinner : (1-t)*⟪gradient g z,x-z⟫+t*⟪gradient g z,y-z⟫ = 0 := by
    rw [← inner_smul_right,← inner_smul_right,← inner_add_right]
    have : (1-t) • (x-z)+t • (y-z) = 0 := by dsimp [z]; module
    rw [this,inner_zero_right]
  rw [hzx] at h1
  rw [hzy] at h2
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h1 h2
  dsimp [z] at *
  nlinarith
private lemma growth {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ) (hsc : StronglyConvexWith g m)
    (hc : ConvexOn ℝ D h) (star x : EuclideanSpace ℝ (Fin n))
    (hs : IsMinimizer g D h star) (hx : x ∈ D) :
    m/4*‖x-star‖^2 ≤ (g x+h x)-(g star+h star) := by
  have hm := hc.1 hx hs.1 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
  have hh := hc.2 hx hs.1 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
  have hg := strong_chord g m hsc x star (1/2) (by norm_num) (by norm_num)
  norm_num only at hg hh
  have hh' := hs.2 _ hm
  simp only [smul_eq_mul] at hh
  nlinarith
private lemma pred_gap {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m M κ : ℝ) (hsc : StronglyConvexWith g m)
    (hc : ConvexOn ℝ D h) (hm : 0 ≤ m) (hk0 : 0 < κ) (hk1 : κ ≤ 1) (hkM : κ*M ≤ m)
    (star x : EuclideanSpace ℝ (Fin n)) (hs : star ∈ D) (hx : x ∈ D)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n))
    (hH : IsBoundedBetween H m M) (hd : IsSearchDirection g D h x H d) :
    predDecrease g h x d ≤ -κ*((g x+h x)-(g star+h star)) := by
  have hc' := convex_step D h hc x (star-x) hx (by simpa using hs) κ hk0.le hk1
  have hd' := hd.2 (κ • (star-x)) hc'.1
  have hg := hsc x star
  have hb := (hH.2 (star-x)).2
  have hq := (hH.2 d).1
  have hz : 0 ≤ ⟪H d,d⟫ := le_trans (mul_nonneg hm (sq_nonneg _)) hq
  simp only [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial] at hd'
  simp only [add_sub_cancel] at hc'
  rw [norm_sub_rev star x] at hb
  have hkk : 0 ≤ κ^2 := sq_nonneg _
  have hb' := mul_le_mul_of_nonneg_left hb hkk
  have hkm := mul_le_mul_of_nonneg_left hkM (mul_nonneg hk0.le (sq_nonneg ‖x-star‖))
  have hg' := mul_le_mul_of_nonneg_left hg hk0.le
  dsimp [predDecrease]
  nlinarith [hc'.2]

private lemma uniform_step {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (L m α β : ℝ)
    (hg : Differentiable ℝ g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (hc : ConvexOn ℝ D h)
    (hm : 0 < m) (ha : α < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ (x : EuclideanSpace ℝ (Fin n))
      (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      x ∈ D → (∀ v, m*‖v‖^2 ≤ ⟪H v,v⟫) → IsSearchDirection g D h x H d →
      IsBacktrackingStep g D h α β x d t → τ ≤ t := by
  have hLp : 0 < L+1 := by linarith
  have he : 0 < (m/2*(1-α))/(L+1) := by positivity
  obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one he hb1
  refine ⟨β^J,pow_pos hb0 _,pow_le_one₀ hb0.le hb1.le,?_⟩
  intro x H d t hx hH hd ht
  obtain ⟨j,rfl,hj,hmin⟩ := ht
  have hstep : SufficientDescent g D h α x d (β^J) := by
    apply short_descent g D h L m α hg hL hlip hc hm ha x H d hx hH hd _
      (pow_pos hb0 _) (pow_le_one₀ hb0.le hb1.le)
    have hJ' := (lt_div_iff₀ hLp).mp hJ
    nlinarith [pow_pos hb0 J]
  have hjJ : j ≤ J := by by_contra hh; exact hmin J (by omega) hstep
  exact (pow_le_pow_iff_right_of_lt_one₀ hb0 hb1).mpr hjJ
private theorem global_converges {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m M L α β : ℝ)
    (hg : Differentiable ℝ g) (hm : 0 < m) (hsc : StronglyConvexWith g m)
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖)
    (hc : ConvexOn ℝ D h) (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (ha0 : 0 < α) (ha1 : α < 1/2) (hb0 : 0 < β) (hb1 : β < 1) (hmM : m ≤ M)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H d t) (hHb : ∀ k, IsBoundedBetween (H k) m M) :
    Tendsto x atTop (𝓝 star) := by
  have hx : ∀ k, x k ∈ D := by
    intro k; cases k with
    | zero => exact hrun.1
    | succ k =>
      obtain ⟨j,hj,hdesc,_⟩ := (hrun.2 k).2.2.1
      rw [(hrun.2 k).2.2.2,hj]
      exact descent_domain g h D α _ _ _ hdesc
  obtain ⟨τ,hτ0,hτ1,hτ⟩ := uniform_step g h D L m α β hg hL hlip hc hm (by linarith) hb0 hb1
  let κ := m/(M+m)
  have hMp : 0 < M+m := by linarith
  have hk0 : 0 < κ := div_pos hm hMp
  have hk1 : κ ≤ 1 := (div_le_one hMp).mpr (by linarith)
  have hkM : κ*M ≤ m := by
    dsimp [κ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hMp).mpr
    nlinarith
  let q := 1-α*τ*κ
  have hq0 : 0 ≤ q := by
    have h1 := mul_le_mul_of_nonneg_left hτ1 ha0.le
    have h2 := mul_le_mul_of_nonneg_right hk1 (mul_nonneg ha0.le hτ0.le)
    dsimp [q]
    nlinarith
  have hq1 : q < 1 := by dsimp [q]; nlinarith [mul_pos (mul_pos ha0 hτ0) hk0]
  let gap := fun k => (g (x k)+h (x k))-(g star+h star)
  have hgap0 : ∀ k, 0 ≤ gap k := by intro k; exact sub_nonneg.mpr (hs.2 _ (hx k))
  have hstep : ∀ k, gap (k+1) ≤ q*gap k := by
    intro k
    have hpred := pred_gap g h D m M κ hsc hc hm.le hk0 hk1 hkM star (x k) hs.1 (hx k) (H k) (d k) (hHb k) (hrun.2 k).2.1
    obtain ⟨j,htj,hdesc,_⟩ := (hrun.2 k).2.2.1
    have ht0 : 0 < t k := htj ▸ pow_pos hb0 _
    have hτt := hτ (x k) (H k) (d k) (t k) (hx k) (fun v => (hHb k).2 v |>.1) (hrun.2 k).2.1 (hrun.2 k).2.2.1
    rw [← htj] at hdesc
    have hval : g (x (k+1))+h (x (k+1)) ≤ g (x k)+h (x k)+α*t k*predDecrease g h (x k) (d k) := by
      rw [(hrun.2 k).2.2.2]
      simpa only [SufficientDescent,compositeObj,if_pos (descent_domain g h D α _ _ _ hdesc),EReal.coe_le_coe_iff] using hdesc
    have hp := mul_le_mul_of_nonneg_left hpred (mul_nonneg ha0.le ht0.le)
    have ht := mul_le_mul_of_nonneg_right hτt (mul_nonneg (mul_nonneg ha0.le hk0.le) (hgap0 k))
    dsimp [q,gap] at *
    nlinarith
  have hgeom : ∀ k, gap k ≤ gap 0*q^k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      calc
        gap (k+1) ≤ q*gap k := hstep k
        _ ≤ q*(gap 0*q^k) := mul_le_mul_of_nonneg_left ih hq0
        _ = gap 0*q^(k+1) := by rw [pow_succ]; ring
  have hnorm : ∀ k, ‖x k-star‖^2 ≤ (4/m*gap 0)*q^k := by
    intro k
    have hgrowth := growth g h D m hsc hc star (x k) hs (hx k)
    have hh := hgeom k
    have hg : m/4*‖x k-star‖^2 ≤ gap 0*q^k := hgrowth.trans hh
    have : ‖x k-star‖^2 ≤ (gap 0*q^k)/(m/4) :=
      (le_div_iff₀ (show 0 < m/4 by positivity)).mpr (by nlinarith [hg])
    convert this using 1 <;> field_simp <;> ring
  have hlim : Tendsto (fun k => ‖x k-star‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) hnorm
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (4/m*gap 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hlim.sqrt
end PNProof

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m M L1 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinimizer g D h xstar)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1) (hmM : m ≤ M)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H Δ t)
    (hHb : ∀ k : ℕ, IsBoundedBetween (H k) m M) :
    Tendsto x atTop (𝓝 xstar) := by
  exact PNProof.global_converges g h D m M L1 α β (hg.differentiable (by norm_num)) hm hsc hL1 hgL hD.2.2.1 xstar hstar hα hα2 hβ hβ1 hmM x H Δ t hrun hHb
