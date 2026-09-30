-- Prove2me | solution 1 for ProxNewton.Exact.prox_newton_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:39:44.05709+00:00
-- url     : https://prove2.me/submissions/c7e23ae6-9d31-4978-8416-0669244bdecf

import Definitions.Def_ProxNewton_Exact_Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
private theorem grad_diff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
    (hfder.differentiable (by norm_num))


private theorem hessian_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x : E) :
    (fderiv ℝ (gradient F) x).toLinearMap.IsSymmetric := by
  have hG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have he := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x
    (hG x).hasFDerivAt
  change HasFDerivAt ((InnerProductSpace.toDual ℝ E) ∘ gradient F) _ x at he
  rw [toDual_comp_gradient] at he
  intro u v
  have hs := ((hF.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)).eq u v
  rw [he.fderiv] at hs
  change ⟪fderiv ℝ (gradient F) x u,v⟫ = ⟪fderiv ℝ (gradient F) x v,u⟫ at hs
  exact hs.trans (real_inner_comm _ _)


private lemma grad_mono {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hsc : StronglyConvexWith g m) (x y : EuclideanSpace ℝ (Fin n)) :
    m*‖x-y‖^2 ≤ ⟪gradient g x-gradient g y,x-y⟫ := by
  have h1 := hsc x y
  have h2 := hsc y x
  rw [norm_sub_rev y x] at h2
  have he : y-x = -(x-y) := by abel
  rw [he,inner_neg_right] at h1
  rw [inner_sub_left]
  linarith
private lemma hessian_lower {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ)
    (hg : ContDiff ℝ 2 g) (hsc : StronglyConvexWith g m) (x v : EuclideanSpace ℝ (Fin n)) :
    m*‖v‖^2 ≤ ⟪hessian g x v,v⟫ := by
  let f : ℝ → ℝ := fun t => ⟪gradient g (x+t • v),v⟫
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd : HasDerivAt f ⟪hessian g x v,v⟫ 0 := by
    have hh := (grad_diff g hg (x+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
    convert! hh.inner ℝ (hasDerivAt_const (0:ℝ) v) using 1 <;> simp [f,hessian]
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hm := grad_mono g m hsc (x+t • v) x
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,mul_pow,inner_smul_right,inner_sub_left] at hm
  change m*‖v‖^2 ≤ t⁻¹*(f (0+t)-f 0)
  simp only [f,zero_add,zero_smul,add_zero]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ ht0).mpr
  exact (mul_le_mul_iff_left₀ ht0).mp (by nlinarith [hm])
private lemma hessian_norm {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (x : EuclideanSpace ℝ (Fin n)) :
    ‖hessian g x‖ ≤ L := norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun y => hlip y x))
private lemma grad_taylor {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hg : ContDiff ℝ 2 g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    ‖gradient g (x+d)-gradient g x-hessian g x d‖ ≤ L/2*‖d‖^2 := by
  let f : ℝ → EuclideanSpace ℝ (Fin n) := fun t => gradient g (x+t • d)-gradient g x-t • hessian g x d
  let B : ℝ → ℝ := fun t => L/2*‖d‖^2*t^2
  have hd (t : ℝ) : HasDerivAt f ((hessian g (x+t • d)-hessian g x) d) t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh := (grad_diff g hg (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    convert! (hh.sub_const (gradient g x)).sub ((hasDerivAt_id t).smul_const (hessian g x d)) using 1 <;> simp [f,hessian]
  have hB (t : ℝ) : HasDerivAt B (L*‖d‖^2*t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_mul (L/2*‖d‖^2) using 1 <;> dsimp only [B,id_eq] <;> ring
  have hh := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0:ℝ)) (b := 1) (fun t ht => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => (hd t).hasDerivWithinAt) (B := B) (B' := fun t => L*‖d‖^2*t)
    (by simp [f,B]) hB (by
      intro t ht
      have hb := (hessian g (x+t • d)-hessian g x).le_opNorm d
      have hl := hlip (x+t • d) x
      simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hl
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]))
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa [f,B] using hh
private lemma scalar_taylor {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hg : ContDiff ℝ 2 g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    g (x+d) ≤ g x+⟪gradient g x,d⟫+1/2*⟪hessian g x d,d⟫+L/6*‖d‖^3 := by
  let f : ℝ → ℝ := fun t => g (x+t • d)-g x-t*⟪gradient g x,d⟫-t^2/2*⟪hessian g x d,d⟫
  let B : ℝ → ℝ := fun t => L/6*‖d‖^3*t^3
  have hd (t : ℝ) : HasDerivAt f ⟪gradient g (x+t • d)-gradient g x-hessian g x (t • d),d⟫ t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh := (hg.differentiable (by norm_num) (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    rw [← inner_gradient_left] at hh
    convert! ((hh.sub_const (g x)).sub ((hasDerivAt_id t).mul_const ⟪gradient g x,d⟫)).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const ⟪hessian g x d,d⟫) using 1 <;>
      simp only [f,Pi.sub_apply,id_eq,map_smul,inner_sub_left,real_inner_smul_left] <;> ring
  have hB (t : ℝ) : HasDerivAt B (L/2*‖d‖^3*t^2) t := by
    convert! ((hasDerivAt_id t).pow 3).const_mul (L/6*‖d‖^3) using 1 <;> dsimp only [B,id_eq] <;> ring
  have hh := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0:ℝ)) (b := 1) (fun t ht => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => (hd t).hasDerivWithinAt) (B := B) (B' := fun t => L/2*‖d‖^3*t^2)
    (by simp [f,B]) hB (by
      intro t ht
      have hb := norm_inner_le_norm (𝕜 := ℝ) (gradient g (x+t • d)-gradient g x-hessian g x (t • d)) d
      have hl := grad_taylor g L hg hL hlip x (t • d)
      simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hl
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]))
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have hr := le_trans (le_abs_self (f 1)) hh
  simp only [f,B,one_smul,one_pow,one_mul,mul_one] at hr
  linarith
private lemma linear_perturbation (A B : ℝ) (h : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ A+t*B) : 0 ≤ A := by
  have ht : Tendsto (fun t : ℝ => A+t*B) (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous (fun t : ℝ => A+t*B) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  exact h t ht.1 ht.2

private lemma model_variational {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hc : ConvexOn ℝ D h)
    (x : EuclideanSpace ℝ (Fin n)) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric)
    (hd : IsSearchDirection g D h x H d) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ D) :
    h (x+d)+⟪-(gradient g x+H d),y-(x+d)⟫ ≤ h y := by
  let v := y-(x+d)
  have hs : ⟪H v,d⟫ = ⟪H d,v⟫ := (hH v d).trans (real_inner_comm _ _)
  have hA : 0 ≤ ⟪gradient g x+H d,v⟫+h y-h (x+d) := by
    apply linear_perturbation _ (⟪H v,v⟫/2)
    intro t ht0 ht1
    have hc' := convex_step D h hc (x+d) v hd.1 (by simpa [v] using hy) t ht0.le ht1.le
    have he : x+(d+t • v) = (x+d)+t • v := by abel
    have hh := hd.2 (d+t • v) (by simpa only [he] using hc'.1)
    rw [he] at hh
    have he' : x+d+v = y := by dsimp [v]; abel
    rw [he'] at hc'
    simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
      inner_smul_right,starRingEnd_apply,star_trivial,hs] at hh
    rw [inner_add_left]
    have hp : 0 ≤ t*(⟪gradient g x,v⟫+⟪H d,v⟫+h y-h (x+d)+t*(⟪H v,v⟫/2)) := by nlinarith [hc'.2]
    exact nonneg_of_mul_nonneg_right hp ht0
  simp only [inner_neg_left]
  change h (x+d)-⟪gradient g x+H d,v⟫ ≤ h y
  linarith
private lemma strong_pred {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hc : ConvexOn ℝ D h)
    (x : EuclideanSpace ℝ (Fin n)) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric)
    (hx : x ∈ D) (hd : IsSearchDirection g D h x H d) :
    predDecrease g h x d ≤ -⟪H d,d⟫ := by
  have hh := model_variational g h D hc x H d hH hd x hx
  have he : x-(x+d) = -d := by abel
  rw [he,inner_neg_right,inner_neg_left,neg_neg,inner_add_left] at hh
  dsimp [predDecrease]
  linarith
private lemma optimal_variational {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hc : ConvexOn ℝ D h) (hg : Differentiable ℝ g)
    (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ D) :
    h star+⟪-gradient g star,y-star⟫ ≤ h y := by
  let v := y-star
  let f : ℝ → ℝ := fun t => g (star+t • v)
  have hl : HasDerivAt (fun t : ℝ => star+t • v) v 0 := by simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add star
  have hd : HasDerivAt f ⟪gradient g star,v⟫ 0 := by
    have hh := (hg (star+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
    convert! hh using 1 <;> simp [f,inner_gradient_left]
  have hh : h star-h y ≤ ⟪gradient g star,v⟫ := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have hc' := convex_step D h hc star v hs.1 (by simpa [v] using hy) t ht.1.le ht.2.le
    have hmin := hs.2 _ hc'.1
    have he : star+v = y := by dsimp [v]; abel
    rw [he] at hc'
    change h star-h y ≤ t⁻¹*(f (0+t)-f 0)
    simp only [f,zero_add,zero_smul,add_zero]
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht.1).mpr
    nlinarith [hc'.2]
  simp only [inner_neg_left]
  change h star-⟪gradient g star,v⟫ ≤ h y
  linarith
private lemma newton_error {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m L : ℝ) (hm : 0 < m)
    (hg : ContDiff ℝ 2 g) (hsc : StronglyConvexWith g m) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖) (hc : ConvexOn ℝ D h)
    (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (x d : EuclideanSpace ℝ (Fin n)) (hd : IsSearchDirection g D h x (hessian g x) d) :
    ‖x+d-star‖ ≤ L/(2*m)*‖x-star‖^2 := by
  have h1 := model_variational g h D hc x (hessian g x) d (hessian_symmetric g hg x) hd star hs.1
  have h2 := optimal_variational g h D hc (hg.differentiable (by norm_num)) star hs (x+d) hd.1
  let e := x+d-star
  let r := gradient g star-gradient g x-hessian g x (star-x)
  have he : star-(x+d) = -e := by dsimp [e]; abel
  rw [he,inner_neg_left,inner_neg_right,neg_neg] at h1
  rw [inner_neg_left] at h2
  have hb := hessian_lower g m hg hsc x e
  have hr : ‖r‖ ≤ L/2*‖x-star‖^2 := by
    simpa [r,norm_sub_rev] using grad_taylor g L hg hL hlip x (star-x)
  have hve : gradient g x+hessian g x d-gradient g star = hessian g x e-r := by
    dsimp [e,r]
    simp only [map_sub,map_add]
    module
  have hip : ⟪hessian g x e,e⟫ ≤ ⟪r,e⟫ := by
    have ha : ⟪gradient g x+hessian g x d-gradient g star,e⟫ ≤ 0 := by rw [inner_sub_left]; linarith [h1,h2]
    rw [hve,inner_sub_left] at ha
    linarith
  have hbound : m*‖e‖^2 ≤ (L/2*‖x-star‖^2)*‖e‖ :=
    hb.trans (hip.trans ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))))
  by_cases he0 : ‖e‖ = 0
  · change ‖e‖ ≤ _
    rw [he0]
    positivity
  · have hep : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he0)
    have hh : m*‖e‖ ≤ L/2*‖x-star‖^2 := (mul_le_mul_iff_right₀ hep).mp (by nlinarith [hbound])
    change ‖e‖ ≤ _
    have hh' : ‖e‖ ≤ (L/2*‖x-star‖^2)/m := (le_div_iff₀ hm).mpr (by nlinarith [hh])
    convert hh' using 1 <;> field_simp <;> ring

private lemma unit_descent {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m L α ε : ℝ)
    (hg : ContDiff ℝ 2 g) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖) (hc : ConvexOn ℝ D h)
    (ha : α < 1/2) (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsLowerBounded H m) (hd : IsSearchDirection g D h x H d)
    (he : ‖(hessian g x-H) d‖ ≤ ε*‖d‖) (hsmall : ε/2+L/6*‖d‖ ≤ (1/2-α)*m) :
    SufficientDescent g D h α x d 1 := by
  have ht := scalar_taylor g L hg hL hlip x d
  have hp := strong_pred g h D hc x H d hH.1 hx hd
  have hb := hH.2 d
  have hi : ⟪hessian g x d,d⟫ ≤ ⟪H d,d⟫+ε*‖d‖^2 := by
    have hh := real_inner_le_norm ((hessian g x-H) d) d
    have hmul := mul_le_mul_of_nonneg_right he (norm_nonneg d)
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left] at hh hmul
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖d‖)
  have hhb := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1/2-α by linarith)
  have hpp := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-α by linarith)
  have hv : g (x+d)+h (x+d) ≤ g x+h x+α*predDecrease g h x d := by
    dsimp [predDecrease] at *
    nlinarith
  unfold SufficientDescent compositeObj
  simp only [one_smul,mul_one]
  split_ifs with hx1
  · exact_mod_cast hv
  · exact False.elim (hx1 (by simpa using hd.1))
private lemma accept_unit {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (α β : ℝ) (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : IsBacktrackingStep g D h α β x d t) (h1 : SufficientDescent g D h α x d 1) : t = 1 := by
  obtain ⟨j,rfl,hj,hn⟩ := ht
  have hj0 : j = 0 := by by_contra hh; exact hn 0 (Nat.pos_of_ne_zero hh) (by simpa using h1)
  simp [hj0]
private lemma hessian_between {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m L : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L*‖x-y‖) (x : EuclideanSpace ℝ (Fin n)) :
    IsBoundedBetween (hessian g x) m (m+L) := by
  refine ⟨hessian_symmetric g hg x,fun v => ⟨hessian_lower g m hg hsc x v,?_⟩⟩
  have hn := (hessian g x).le_opNorm v
  have hh := hessian_norm g L hL hlip x
  have hi := real_inner_le_norm (hessian g x v) v
  have he := mul_le_mul_of_nonneg_right hh (norm_nonneg v)
  have hf := mul_le_mul_of_nonneg_right (hn.trans he) (norm_nonneg v)
  nlinarith [mul_nonneg hm.le (sq_nonneg ‖v‖)]
private lemma residual_error {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ) (hm : 0 < m) (hg : Differentiable ℝ g)
    (hsc : StronglyConvexWith g m) (hc : ConvexOn ℝ D h)
    (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (x : EuclideanSpace ℝ (Fin n)) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric) (hd : IsSearchDirection g D h x H d) :
    m*‖x+d-star‖ ≤ ‖gradient g (x+d)-gradient g x-H d‖ := by
  have h1 := model_variational g h D hc x H d hH hd star hs.1
  have h2 := optimal_variational g h D hc hg star hs (x+d) hd.1
  let e := x+d-star
  have he : star-(x+d) = -e := by dsimp [e]; abel
  rw [he,inner_neg_left,inner_neg_right,neg_neg] at h1
  rw [inner_neg_left] at h2
  have hb := grad_mono g m hsc (x+d) star
  have hi := real_inner_le_norm (gradient g (x+d)-gradient g x-H d) e
  simp only [inner_sub_left,inner_add_left] at h1 hb hi
  change m*‖e‖ ≤ _
  by_cases he0 : ‖e‖ = 0
  · simp [he0]
  · have hep : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he0)
    apply (mul_le_mul_iff_right₀ hep).mp
    dsimp [e] at *
    nlinarith [h1,h2,hb,hi]
private lemma run_mem {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H d t) : ∀ k, x k ∈ D := by
  intro k; cases k with
  | zero => exact hrun.1
  | succ k =>
    obtain ⟨j,hj,hdesc,_⟩ := (hrun.2 k).2.2.1
    rw [(hrun.2 k).2.2.2,hj]
    exact descent_domain g h D α _ _ _ hdesc
private lemma direction_zero {n : ℕ} (x d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (star : EuclideanSpace ℝ (Fin n)) (hx : Tendsto x atTop (𝓝 star))
    (τ : ℝ) (hτ : 0 < τ) (ht : ∀ k, τ ≤ t k) (hrec : ∀ k, x (k+1) = x k+t k • d k) :
    Tendsto (fun k => ‖d k‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun k => ‖x (k+1)-x k‖/τ) atTop (𝓝 0) := by
    simpa using (((hx.comp (tendsto_add_atTop_nat 1)).sub hx).norm).div_const τ
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hi
  apply (le_div_iff₀ hτ).mpr
  rw [hrec k,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (lt_of_lt_of_le hτ (ht k))]
  nlinarith [mul_le_mul_of_nonneg_right (ht k) (norm_nonneg (d k))]
private lemma dm_direction {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (star : EuclideanSpace ℝ (Fin n)) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ht : ∀ k, 0 < t k) (hrec : ∀ k, x (k+1) = x k+t k • d k) (hDM : DennisMore g star x H) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖(H k-hessian g star) (d k)‖ ≤ ε*‖d k‖ := by
  intro ε he
  filter_upwards [hDM ε he] with k hk
  rw [hrec k,add_sub_cancel_left,map_smul,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (ht k)] at hk
  apply (mul_le_mul_iff_left₀ (ht k)).mp
  nlinarith [hk]
private lemma dm_local {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖)
    (star : EuclideanSpace ℝ (Fin n)) (x d : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hx : Tendsto x atTop (𝓝 star))
    (hDM : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖(H k-hessian g star) (d k)‖ ≤ ε*‖d k‖) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖(hessian g (x k)-H k) (d k)‖ ≤ ε*‖d k‖ := by
  intro ε he
  have hx0 := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hc : ∀ᶠ k in atTop, L*‖x k-star‖ < ε/2 := by
    exact (show Tendsto (fun k => L*‖x k-star‖) atTop (𝓝 0) by simpa using hx0.const_mul L).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hDM (ε/2) (by positivity),hc] with k hk hdist
  have hn := (hessian g (x k)-hessian g star).le_opNorm (d k)
  have hl := hlip (x k) star
  have heq : (hessian g (x k)-H k) (d k) = (hessian g (x k)-hessian g star) (d k)-(H k-hessian g star) (d k) := by simp
  rw [heq]
  apply (norm_sub_le _ _).trans
  have h1 := mul_le_mul_of_nonneg_right hl (norm_nonneg (d k))
  have h2 := mul_le_mul_of_nonneg_right hdist.le (norm_nonneg (d k))
  linarith
private lemma eventual_unit {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m L α : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L*‖x-y‖) (hc : ConvexOn ℝ D h)
    (ha : α < 1/2) (x d : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x k ∈ D) (hH : ∀ k, IsLowerBounded (H k) m)
    (hd : ∀ k, IsSearchDirection g D h (x k) (H k) (d k))
    (hd0 : Tendsto (fun k => ‖d k‖) atTop (𝓝 0))
    (he : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖(hessian g (x k)-H k) (d k)‖ ≤ ε*‖d k‖) :
    ∀ᶠ k in atTop, SufficientDescent g D h α (x k) (d k) 1 := by
  let ε := (1/2-α)*m
  have he0 : 0 < ε := mul_pos (by linarith) hm
  have hl : ∀ᶠ k in atTop, L/6*‖d k‖ < ε/2 := by
    exact (show Tendsto (fun k => L/6*‖d k‖) atTop (𝓝 0) by simpa using hd0.const_mul (L/6)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [he ε he0,hl] with k hk hlk
  exact unit_descent g h D m L α ε hg hL hlip hc ha (x k) (H k) (d k) (hx k) (hH k) (hd k) hk (by dsimp [ε] at *; linarith)


private theorem quasi_results {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m M L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L1*‖x-y‖) (hL2 : 0 ≤ L2)
    (hHL : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L2*‖x-y‖) (hc : ConvexOn ℝ D h)
    (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (ha0 : 0 < α) (ha1 : α < 1/2) (hb0 : 0 < β) (hb1 : β < 1) (hmM : m ≤ M)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonTypeRun g D h α β x H d t) (hHb : ∀ k, IsBoundedBetween (H k) m M)
    (hDM : DennisMore g star x H) :
    Tendsto x atTop (𝓝 star) ∧ (∀ᶠ k in atTop, SufficientDescent g D h α (x k) (d k) 1) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k+1)-star‖ ≤ ε*‖x k-star‖ := by
  have hdg := hg.differentiable (by norm_num)
  have hlim := global_converges g h D m M L1 α β hdg hm hsc hL1 hgL hc star hs ha0 ha1 hb0 hb1 hmM x H d t hrun hHb
  have hmem := run_mem g h D α β x H d t hrun
  obtain ⟨τ,hτ0,hτ1,hτ⟩ := uniform_step g h D L1 m α β hdg hL1 hgL hc hm (by linarith) hb0 hb1
  have htτ : ∀ k, τ ≤ t k := fun k => hτ (x k) (H k) (d k) (t k) (hmem k)
    (fun v => (hHb k).2 v |>.1) (hrun.2 k).2.1 (hrun.2 k).2.2.1
  have htpos : ∀ k, 0 < t k := fun k => lt_of_lt_of_le hτ0 (htτ k)
  have hrec : ∀ k, x (k+1) = x k+t k • d k := fun k => (hrun.2 k).2.2.2
  have hdlim := direction_zero x d t star hlim τ hτ0 htτ hrec
  have hDM' := dm_local g L2 hL2 hHL star x d H hlim (dm_direction g star x d t H htpos hrec hDM)
  have hunit := eventual_unit g h D m L2 α hg hm hL2 hHL hc ha1 x d H hmem
    (fun k => ⟨(hHb k).1,fun v => (hHb k).2 v |>.1⟩) (fun k => (hrun.2 k).2.1) hdlim hDM'
  refine ⟨hlim,hunit,?_⟩
  intro ε he0
  let c := m*ε/(2*(1+ε))
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c < m := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+ε))).mpr
    nlinarith [mul_pos hm he0]
  have hce : c ≤ ε*(m-c) := by
    have heq : c*(2*(1+ε)) = m*ε := by dsimp [c]; field_simp
    nlinarith [mul_pos hm he0]
  have hdn : ∀ᶠ k in atTop, L2/2*‖d k‖ < c/2 := by
    exact (show Tendsto (fun k => L2/2*‖d k‖) atTop (𝓝 0) by simpa using hdlim.const_mul (L2/2)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hunit,hDM' (c/2) (by positivity),hdn] with k hu hdk hsmall
  have ht1 := accept_unit g h D α β (x k) (d k) (t k) (hrun.2 k).2.2.1 hu
  have hxnext : x (k+1) = x k+d k := by simpa only [ht1,one_smul] using hrec k
  have hres := residual_error g h D m hm hdg hsc hc star hs (x k) (H k) (d k) (hHb k).1 (hrun.2 k).2.1
  have htay := grad_taylor g L2 hg hL2 hHL (x k) (d k)
  have heq : gradient g (x k+d k)-gradient g (x k)-H k (d k) =
      (gradient g (x k+d k)-gradient g (x k)-hessian g (x k) (d k))+(hessian g (x k)-H k) (d k) := by simp
  have hnorm : ‖gradient g (x k+d k)-gradient g (x k)-H k (d k)‖ ≤ c*‖d k‖ := by
    rw [heq]
    have hn := norm_add_le (gradient g (x k+d k)-gradient g (x k)-hessian g (x k) (d k)) ((hessian g (x k)-H k) (d k))
    have hh := mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg (d k))
    nlinarith
  have htri : ‖d k‖ ≤ ‖x k+d k-star‖+‖x k-star‖ := by
    have he : d k = (x k+d k-star)-(x k-star) := by abel
    calc
      ‖d k‖ = ‖(x k+d k-star)-(x k-star)‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hc := mul_le_mul_of_nonneg_left htri hc0.le
  rw [hxnext]
  apply (mul_le_mul_iff_left₀ (show 0 < m-c by linarith)).mp
  have hh := mul_le_mul_of_nonneg_right hce (norm_nonneg (x k-star))
  nlinarith
private theorem newton_results {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (m L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y, ‖gradient g x-gradient g y‖ ≤ L1*‖x-y‖) (hL2 : 0 ≤ L2)
    (hHL : ∀ x y, ‖hessian g x-hessian g y‖ ≤ L2*‖x-y‖) (hc : ConvexOn ℝ D h)
    (star : EuclideanSpace ℝ (Fin n)) (hs : IsMinimizer g D h star)
    (ha0 : 0 < α) (ha1 : α < 1/2) (hb0 : 0 < β) (hb1 : β < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (hrun : IsProxNewtonRun g D h α β x H d t) :
    Tendsto x atTop (𝓝 star) ∧ (∀ᶠ k in atTop, SufficientDescent g D h α (x k) (d k) 1) ∧
    ∀ᶠ k in atTop, ‖x (k+1)-star‖ ≤ L2/(2*m)*‖x k-star‖^2 := by
  have hHb : ∀ k, IsBoundedBetween (H k) m (m+L1) := by
    intro k
    rw [hrun.2 k]
    exact hessian_between g m L1 hg hm hsc hL1 hgL (x k)
  have hlim := global_converges g h D m (m+L1) L1 α β (hg.differentiable (by norm_num)) hm hsc hL1 hgL hc star hs ha0 ha1 hb0 hb1 (by linarith) x H d t hrun.1 hHb
  have hDM : DennisMore g star x H := by
    intro ε he
    have hx0 := tendsto_iff_norm_sub_tendsto_zero.mp hlim
    have hc : ∀ᶠ k in atTop, L2*‖x k-star‖ < ε := by
      exact (show Tendsto (fun k => L2*‖x k-star‖) atTop (𝓝 0) by simpa using hx0.const_mul L2).eventually (gt_mem_nhds he)
    filter_upwards [hc] with k hk
    rw [hrun.2 k]
    have hn := (hessian g (x k)-hessian g star).le_opNorm (x (k+1)-x k)
    have hl := hHL (x k) star
    have hh := mul_le_mul_of_nonneg_right (hl.trans hk.le) (norm_nonneg (x (k+1)-x k))
    exact hn.trans hh
  have hq := quasi_results g h D m (m+L1) L1 L2 α β hg hm hsc hL1 hgL hL2 hHL hc star hs ha0 ha1 hb0 hb1 (by linarith) x H d t hrun.1 hHb hDM
  refine ⟨hlim,hq.2.1,?_⟩
  filter_upwards [hq.2.1] with k hk
  have ht1 := accept_unit g h D α β (x k) (d k) (t k) (hrun.1.2 k).2.2.1 hk
  rw [(hrun.1.2 k).2.2.2,ht1,one_smul]
  exact newton_error g h D m L2 hm hg hsc hL2 hHL hc star hs (x k) (d k) (by simpa only [hrun.2 k] using (hrun.1.2 k).2.1)
end PNProof

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (m L1 L2 α β : ℝ)
    (hg : ContDiff ℝ 2 g) (hm : 0 < m) (hsc : StronglyConvexWith g m) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hL2 : 0 ≤ L2)
    (hHL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinimizer g D h xstar)
    (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (hrun : IsProxNewtonRun g D h α β x H Δ t) :
    Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ L2 / (2 * m) * ‖x k - xstar‖ ^ 2 := by
  have hh := PNProof.newton_results g h D m L1 L2 α β hg hm hsc hL1 hgL hL2 hHL hD.2.2.1 xstar hstar hα hα2 hβ hβ1 x H Δ t hrun
  exact ⟨hh.1,hh.2.2⟩
