-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.eq2_6_fejer_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:17:37.340568+00:00
-- url     : https://prove2.me/submissions/8df5298e-7999-4e2e-b4b4-e2e47e86d4ea

import Definitions.Def_SolodovSvaiterVI_Alg21_IsAlg21Run
import Definitions.Def_SolodovSvaiterVI_Alg21_SatisfiesCond12
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic
open SolodovSvaiterVI.Alg21
open scoped InnerProductSpace

private theorem proj_spec {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x : EuclideanSpace ℝ (Fin n)) :
    projOnto C x∈C ∧ ∀ y∈C, ⟪x-projOnto C x,y-projOnto C x⟫_ℝ ≤ 0 := by
  letI : Nonempty C := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : C => ‖x-y‖)) := ⟨0,by rintro _ ⟨y,rfl⟩; exact norm_nonneg _⟩
  have he : ∃ p∈C, ∀ y∈C, ‖x-p‖ ≤ ‖x-y‖ := by
    obtain ⟨p,hp,heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
    refine ⟨p,hp,?_⟩
    intro y hy
    rw [heq]
    exact ciInf_le hb ⟨y,hy⟩
  have hs : projOnto C x∈C ∧ ∀ y∈C, ‖x-projOnto C x‖ ≤ ‖x-y‖ := by
    simpa only [projOnto,dif_pos he] using Classical.choose_spec he
  refine ⟨hs.1,(norm_eq_iInf_iff_real_inner_le_zero hcv hs.1).mp ?_⟩
  exact le_antisymm (le_ciInf (fun y => hs.2 y y.2)) (ciInf_le hb ⟨_,hs.1⟩)

private theorem proj_eq_of_vi {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x p : EuclideanSpace ℝ (Fin n))
    (hp : p∈C) (hvi : ∀ y∈C, ⟪x-p,y-p⟫_ℝ ≤ 0) : projOnto C x=p := by
  have hq := proj_spec C hne hc hcv x
  have h1 := hq.2 p hp
  have h2 := hvi _ hq.1
  have hn : ‖projOnto C x-p‖^2 ≤ 0 := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2
    rw [real_inner_comm p (projOnto C x)] at h1
    nlinarith [real_inner_comm p (projOnto C x)]
  have hz : ‖projOnto C x-p‖=0 := by nlinarith [norm_nonneg (projOnto C x-p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

private theorem proj_pyth {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x y : EuclideanSpace ℝ (Fin n))
    (hy : y∈C) : ‖projOnto C x-y‖^2 ≤ ‖x-y‖^2-‖x-projOnto C x‖^2 := by
  have h := (proj_spec C hne hc hcv x).2 y hy
  simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h
  simp only [norm_sub_sq_real]
  linarith

private theorem half_closed {n : ℕ} (w z : EuclideanSpace ℝ (Fin n)) : IsClosed (halfspace w z) :=
  isClosed_le (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const

private theorem half_convex {n : ℕ} (w z : EuclideanSpace ℝ (Fin n)) : Convex ℝ (halfspace w z) := by
  intro a ha b hb u v hu hv huv
  change ⟪w,u•a+v•b-z⟫_ℝ ≤ 0
  change ⟪w,a-z⟫_ℝ ≤ 0 at ha
  change ⟪w,b-z⟫_ℝ ≤ 0 at hb
  have hid : ⟪w,u•a+v•b-z⟫_ℝ = u*⟪w,a-z⟫_ℝ+v*⟪w,b-z⟫_ℝ := by
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right]
    nlinarith [congrArg (fun t : ℝ => t*⟪w,z⟫_ℝ) huv]
  rw [hid]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu ha) (mul_nonpos_of_nonneg_of_nonpos hv hb)

private theorem half_projection {n : ℕ} (w z x : EuclideanSpace ℝ (Fin n))
    (ha : 0 < ⟪w,x-z⟫_ℝ) :
    projOnto (halfspace w z) x=x-(⟪w,x-z⟫_ℝ/‖w‖^2)•w ∧
      ⟪w,projOnto (halfspace w z) x-z⟫_ℝ=0 ∧
      ‖x-projOnto (halfspace w z) x‖=⟪w,x-z⟫_ℝ/‖w‖ := by
  have hw : w≠0 := by intro h; subst w; simpa using ha
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let t : ℝ := ⟪w,x-z⟫_ℝ/‖w‖^2
  have ht : 0 < t := div_pos ha (sq_pos_of_pos hn)
  have hid : ⟪w,x-t•w-z⟫_ℝ=0 := by
    simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    have he : t*‖w‖^2=⟪w,x-z⟫_ℝ := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hn))
    rw [inner_sub_right] at he
    linarith
  have hproj : projOnto (halfspace w z) x=x-t•w := by
    apply proj_eq_of_vi _ ⟨z,by simp [halfspace]⟩ (half_closed w z) (half_convex w z)
    · exact le_of_eq hid
    · intro y hy
      have hy' : ⟪w,y-z⟫_ℝ ≤ 0 := hy
      have he : ⟪x-(x-t•w),y-(x-t•w)⟫_ℝ=t*⟪w,y-z⟫_ℝ := by
        rw [sub_sub_cancel]
        simp only [real_inner_smul_left,inner_sub_right] at *
        nlinarith [hid]
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le hy'
  refine ⟨hproj,by rw [hproj]; exact hid,?_⟩
  rw [hproj,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  dsimp [t]
  field_simp

private theorem half_composition {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (w z x : EuclideanSpace ℝ (Fin n))
    (hx : x∈C) (hne : (C∩halfspace w z).Nonempty) (ha : 0 < ⟪w,x-z⟫_ℝ) :
    projOnto (C∩halfspace w z) (projOnto (halfspace w z) x)=projOnto (C∩halfspace w z) x := by
  let p := projOnto (halfspace w z) x
  let q := projOnto (C∩halfspace w z) p
  let a := ⟪w,x-z⟫_ℝ
  let b := ⟪w,q-z⟫_ℝ
  let t := a/‖w‖^2
  have hw : w≠0 := by intro h; subst w; simp at ha
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have ht : 0 < t := div_pos ha (sq_pos_of_pos hn)
  obtain ⟨hp,hpbd,hpnorm⟩ := half_projection w z x ha
  change p=x-t•w at hp
  change ⟪w,p-z⟫_ℝ=0 at hpbd
  have hKc := hCc.inter (half_closed w z)
  have hKcv := hCcv.inter (half_convex w z)
  have hq := proj_spec (C∩halfspace w z) hne hKc hKcv p
  change q∈C∩halfspace w z ∧ ∀ y∈C∩halfspace w z, ⟪p-q,y-q⟫_ℝ ≤ 0 at hq
  have hb : b ≤ 0 := hq.1.2
  have hxx : x-q=(p-q)+t•w := by rw [hp]; module
  have hpw : ⟪p-q,w⟫_ℝ = -b := by
    dsimp [b]
    rw [← real_inner_comm (p-q) w]
    simp only [inner_sub_right] at *
    linarith [hpbd]
  have hb0 : b=0 := by
    by_contra hbne
    have hbneg : b < 0 := lt_of_le_of_ne hb hbne
    let u : ℝ := -b/(2*(a-b))
    have hden : 0 < 2*(a-b) := by dsimp [a]; linarith
    have hu : 0 < u := div_pos (neg_pos.mpr hbneg) hden
    have hu1 : u ≤ 1 := by apply (div_le_one hden).mpr; dsimp [a]; linarith
    let y := (1-u)•q+u•x
    have hyC : y∈C := hCcv hq.1.1 hx (by linarith) hu.le (by ring)
    have hyH : y∈halfspace w z := by
      change ⟪w,y-z⟫_ℝ ≤ 0
      have hy : ⟪w,y-z⟫_ℝ=(1-u)*b+u*a := by
        dsimp [y,a,b]
        simp only [inner_add_right,inner_sub_right,real_inner_smul_right]
        ring
      rw [hy]
      have halg : (1-u)*b+u*a=b/2 := by
        dsimp [u]
        field_simp [ne_of_gt hden,ne_of_gt (by linarith : 0 < a-b)]
        ring
      rw [halg]
      linarith
    have hv := hq.2 y ⟨hyC,hyH⟩
    have hyv : y-q=u•(x-q) := by dsimp [y]; module
    rw [hyv,real_inner_smul_right] at hv
    have hi : 0 < ⟪p-q,x-q⟫_ℝ := by
      rw [hxx,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hpw]
      have hm : 0 < t*(-b) := mul_pos ht (neg_pos.mpr hbneg)
      nlinarith [sq_nonneg ‖p-q‖]
    exact (not_lt_of_ge hv) (mul_pos hu hi)
  have hvi : ∀ y∈C∩halfspace w z, ⟪x-q,y-q⟫_ℝ ≤ 0 := by
    intro y hy
    have hv := hq.2 y hy
    have hwy : ⟪w,y-q⟫_ℝ ≤ 0 := by
      have hyh : ⟪w,y-z⟫_ℝ ≤ 0 := hy.2
      change ⟪w,q-z⟫_ℝ=0 at hb0
      simp only [inner_sub_right] at *
      linarith
    rw [hxx,inner_add_left,real_inner_smul_left]
    exact add_nonpos hv (mul_nonpos_of_nonneg_of_nonpos ht.le hwy)
  exact (proj_eq_of_vi _ hne hKc hKcv x q hq.1 hvi).symm

private theorem step_data {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x∈C) (hr : SolodovSvaiterVI.Alg21.residual F C x≠0) (k : ℕ)
    (hk : ArmijoHolds F C gamma sigma x k) :
    let z := x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x
    z∈C ∧ (∀ xs∈viSol F C, xs∈halfspace (F z) z) ∧ 0 < ⟪F z,x-z⟫_ℝ := by
  dsimp only
  have hCne : C.Nonempty := ⟨x,hx⟩
  have hp := (proj_spec C hCne hCc hCcv (x-F x)).1
  have hη0 : 0 < gamma^k := pow_pos hγ0 _
  have hη1 : gamma^k ≤ 1 := pow_le_one₀ hγ0.le hγ1.le
  have hz : x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x∈C := by
    have hh := hCcv hx hp (by linarith : 0 ≤ 1-gamma^k) hη0.le (by ring : 1-gamma^k+gamma^k=1)
    convert hh using 1
    unfold SolodovSvaiterVI.Alg21.residual
    module
  refine ⟨hz,?_,?_⟩
  · intro xs hxs
    have hh := h12 xs hxs _ hz
    change ⟪F (x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x),xs-(x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x)⟫_ℝ ≤ 0
    simp only [inner_sub_right] at hh ⊢
    linarith
  · have he : x-(x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x)=gamma^k•SolodovSvaiterVI.Alg21.residual F C x := by module
    rw [he,real_inner_smul_right]
    apply mul_pos hη0
    have hn : 0 < ‖SolodovSvaiterVI.Alg21.residual F C x‖ := norm_pos_iff.mpr hr
    exact lt_of_lt_of_le (mul_pos hσ0 (sq_pos_of_pos hn)) hk

private theorem step_fejer {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x∈C) (hr : SolodovSvaiterVI.Alg21.residual F C x≠0) (k : ℕ)
    (hk : ArmijoHolds F C gamma sigma x k) :
    let z := x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x
    let H := halfspace (F z) z
    let xb := projOnto H x
    let xp := projOnto (C∩H) x
    ∀ xs∈viSol F C,
      ‖xp-xs‖^2 ≤ ‖x-xs‖^2-‖xp-xb‖^2-(gamma^k*sigma/‖F z‖)^2*‖SolodovSvaiterVI.Alg21.residual F C x‖^4 := by
  dsimp only
  let z := x-gamma^k•SolodovSvaiterVI.Alg21.residual F C x
  let H := halfspace (F z) z
  let xb := projOnto H x
  let xp := projOnto (C∩H) x
  intro xs hxs
  change ‖xp-xs‖^2 ≤ ‖x-xs‖^2-‖xp-xb‖^2-(gamma^k*sigma/‖F z‖)^2*‖SolodovSvaiterVI.Alg21.residual F C x‖^4
  have hd := step_data F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x hx hr k hk
  change z∈C ∧ (∀ xs∈viSol F C, xs∈H) ∧ 0 < ⟪F z,x-z⟫_ℝ at hd
  have hxH := hd.2.1 xs hxs
  have hne : (C∩H).Nonempty := ⟨xs,hxs.1,hxH⟩
  have hcomp := half_composition C hCc hCcv (F z) z x hx hne hd.2.2
  have h1 := proj_pyth (C∩H) hne (hCc.inter (half_closed _ _)) (hCcv.inter (half_convex _ _)) xb xs ⟨hxs.1,hxH⟩
  rw [hcomp] at h1
  change ‖xp-xs‖^2 ≤ ‖xb-xs‖^2-‖xb-xp‖^2 at h1
  rw [norm_sub_rev xb xp] at h1
  have h2 := proj_pyth H ⟨xs,hxH⟩ (half_closed _ _) (half_convex _ _) x xs hxH
  change ‖xb-xs‖^2 ≤ ‖x-xs‖^2-‖x-xb‖^2 at h2
  have hpn := (half_projection (F z) z x hd.2.2).2.2
  change ‖x-xb‖=⟪F z,x-z⟫_ℝ/‖F z‖ at hpn
  have hw : F z≠0 := by intro he; have ha := hd.2.2; rw [he] at ha; simp at ha
  have hn : 0 < ‖F z‖ := norm_pos_iff.mpr hw
  have hη : 0 < gamma^k := pow_pos hγ0 _
  have hdist : gamma^k*sigma/‖F z‖*‖SolodovSvaiterVI.Alg21.residual F C x‖^2 ≤ ‖x-xb‖ := by
    rw [hpn]
    have he : x-z=gamma^k•SolodovSvaiterVI.Alg21.residual F C x := by dsimp [z]; module
    rw [he,real_inner_smul_right]
    calc
      _ = gamma^k*(sigma*‖SolodovSvaiterVI.Alg21.residual F C x‖^2)/‖F z‖ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hη.le) hn.le
  have hleft : 0 ≤ gamma^k*sigma/‖F z‖*‖SolodovSvaiterVI.Alg21.residual F C x‖^2 := by positivity
  have hsq := (sq_le_sq₀ hleft (norm_nonneg _)).mpr hdist
  have hid : (gamma^k*sigma/‖F z‖*‖SolodovSvaiterVI.Alg21.residual F C x‖^2)^2 =
      (gamma^k*sigma/‖F z‖)^2*‖SolodovSvaiterVI.Alg21.residual F C x‖^4 := by ring
  rw [hid] at hsq
  linarith

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) (hr : SolodovSvaiterVI.Alg21.residual F C x ≠ 0)
    (k : ℕ) (hk : ArmijoHolds F C gamma sigma x k) :
    let z := x - gamma ^ k • SolodovSvaiterVI.Alg21.residual F C x
    let H := halfspace (F z) z
    let xbar := projOnto H x
    let xnext := projOnto (C ∩ H) x
    ∀ xs ∈ viSol F C,
      ‖xnext - xs‖ ^ 2 ≤
        ‖x - xs‖ ^ 2 - ‖xnext - xbar‖ ^ 2 -
          (gamma ^ k * sigma / ‖F z‖) ^ 2 * ‖SolodovSvaiterVI.Alg21.residual F C x‖ ^ 4 := by
  exact step_fejer F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x hx hr k hk
