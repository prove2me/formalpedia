-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.theorem2_1_converges_to_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:29:57.370662+00:00
-- url     : https://prove2.me/submissions/bd341e16-dff7-4edc-a980-670deb894734

import Definitions.Def_SolodovSvaiterVI_Alg21_IsAlg21Run
import Definitions.Def_SolodovSvaiterVI_Alg21_SatisfiesCond12
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
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

private theorem run_members {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k) :
    ∀ i, x i∈C := by
  intro i
  induction i with
  | zero => exact hrun.1
  | succ i ih =>
    by_cases hr : SolodovSvaiterVI.Alg21.residual F C (x i)=0
    · rw [(hrun.2 i).1 hr]; exact ih
    · obtain ⟨hk,hstep⟩ := (hrun.2 i).2 hr
      have hd := step_data F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 (x i) ih hr (k i) hk.1
      obtain ⟨xs,hxs⟩ := hS
      have hne : (C∩halfspace (F (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i)))
          (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i))).Nonempty := ⟨xs,hxs.1,hd.2.1 xs hxs⟩
      rw [hstep]
      exact (proj_spec _ hne (hCc.inter (half_closed _ _)) (hCcv.inter (half_convex _ _)) (x i)).1.1

private theorem run_decrease {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs∈viSol F C) (i : ℕ) :
    ‖x (i+1)-xs‖^2 ≤ ‖x i-xs‖^2-
      (gamma^(k i)*sigma/‖F (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i))‖)^2*
        ‖SolodovSvaiterVI.Alg21.residual F C (x i)‖^4 := by
  by_cases hr : SolodovSvaiterVI.Alg21.residual F C (x i)=0
  · rw [(hrun.2 i).1 hr,hr]; simp
  · obtain ⟨hk,hstep⟩ := (hrun.2 i).2 hr
    have hmem := run_members F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun i
    have hh := step_fejer F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 (x i) hmem hr (k i) hk.1 xs hxs
    rw [← hstep] at hh
    nlinarith [sq_nonneg ‖x (i+1)-projOnto (halfspace (F (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i)))
      (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i))) (x i)‖]

private theorem run_fejer {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs∈viSol F C) : Antitone (fun i => ‖x i-xs‖) := by
  apply antitone_nat_of_succ_le
  intro i
  have hd := run_decrease F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun xs hxs i
  have he : 0 ≤ (gamma^(k i)*sigma/‖F (x i-gamma^(k i)•SolodovSvaiterVI.Alg21.residual F C (x i))‖)^2*
        ‖SolodovSvaiterVI.Alg21.residual F C (x i)‖^4 := by positivity
  nlinarith [norm_nonneg (x (i+1)-xs),norm_nonneg (x i-xs)]

private theorem root_limit {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : Filter.Tendsto (fun i => (f i)^2) Filter.atTop (nhds 0)) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hh := h.sqrt
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero,abs_of_nonneg (hf _)] using hh

open Filter
open scoped Topology

private theorem proj_nonexpansive {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖projOnto C x-projOnto C y‖ ≤ ‖x-y‖ := by
  have hp := proj_spec C hne hc hcv x
  have hq := proj_spec C hne hc hcv y
  have h1 := hp.2 _ hq.1
  have h2 := hq.2 _ hp.1
  have hsq : ‖projOnto C x-projOnto C y‖^2 ≤ ⟪x-y,projOnto C x-projOnto C y⟫_ℝ := by
    simp only [norm_sub_sq_real,inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at *
    nlinarith [real_inner_comm (projOnto C x) (projOnto C y)]
  have hle := real_inner_le_norm (x-y) (projOnto C x-projOnto C y)
  nlinarith [sq_nonneg (‖projOnto C x-projOnto C y‖-‖x-y‖),norm_nonneg (projOnto C x-projOnto C y),norm_nonneg (x-y)]

private theorem proj_continuous {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) : Continuous (projOnto C) := by
  have hh : LipschitzWith 1 (projOnto C) := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using proj_nonexpansive C hne hc hcv x y)
  exact hh.continuous

private theorem eta_residual_limit {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hF : Continuous F) (hS : (viSol F C).Nonempty)
    (h12 : SatisfiesCond12 F C) (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k) :
    Tendsto (fun i => gamma^(k i)*‖SolodovSvaiterVI.Alg21.residual F C (x i)‖) atTop (𝓝 0) := by
  obtain ⟨xs,hxs⟩ := hS
  have hS : (viSol F C).Nonempty := ⟨xs,hxs⟩
  let r := SolodovSvaiterVI.Alg21.residual F C
  let eta (i : ℕ) := gamma^(k i)
  let z (i : ℕ) := x i-eta i•r (x i)
  let E (i : ℕ) := ‖x i-xs‖^2
  let err (i : ℕ) := (eta i*sigma/‖F (z i)‖)^2*‖r (x i)‖^4
  have herr0 (i : ℕ) : 0 ≤ err i := by dsimp [err]; positivity
  have heta (i : ℕ) : 0 < eta i ∧ eta i ≤ 1 := ⟨pow_pos hγ0 _,pow_le_one₀ hγ0.le hγ1.le⟩
  have hdecr (i : ℕ) : E (i+1) ≤ E i-err i :=
    run_decrease F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun xs hxs i
  have hmono := run_fejer F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun xs hxs
  have hE : Antitone E := by
    intro i j hij
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hmono hij)
  have hEbelow : BddBelow (Set.range E) := ⟨0,by rintro _ ⟨i,rfl⟩; exact sq_nonneg _⟩
  have hEt := tendsto_atTop_ciInf hE hEbelow
  have hgap : Tendsto (fun i => E i-E (i+1)) atTop (𝓝 0) := by
    simpa using hEt.sub (hEt.comp (tendsto_add_atTop_nat 1))
  have herr : Tendsto err atTop (𝓝 0) := squeeze_zero herr0 (fun i => by linarith [hdecr i]) hgap
  have hmem := run_members F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun
  have hrc : Continuous r := continuous_id.sub ((proj_continuous C ⟨xs,hxs.1⟩ hCc hCcv).comp (continuous_id.sub hF))
  let B := Metric.closedBall xs ‖x 0-xs‖
  have hB : IsCompact B := isCompact_closedBall _ _
  have hxB (i : ℕ) : x i∈B := by
    change dist (x i) xs ≤ ‖x 0-xs‖
    rw [dist_eq_norm]
    exact hmono (Nat.zero_le i)
  have hmap : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => F (p.2-p.1•r p.2)) :=
    hF.comp (continuous_snd.sub (continuous_fst.smul (hrc.comp continuous_snd)))
  obtain ⟨M,hM,hMb⟩ := (((isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).prod hB).image hmap).isBounded.exists_pos_norm_le
  have hFi (i : ℕ) : ‖F (z i)‖ ≤ M := hMb _ ⟨(eta i,x i),⟨⟨(heta i).1.le,(heta i).2⟩,hxB i⟩,rfl⟩
  have hbound (i : ℕ) : sigma^2*(eta i*‖r (x i)‖)^4 ≤ M^2*err i := by
    by_cases hr : r (x i)=0
    · simp [hr,err]
    · have hd := step_data F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 (x i) (hmem i) hr (k i) ((hrun.2 i).2 hr).1.1
      have hw : F (z i)≠0 := by
        intro hh
        have hp : 0 < ⟪F (z i),x i-z i⟫_ℝ := hd.2.2
        rw [hh] at hp
        simp at hp
      have hn : ‖F (z i)‖≠0 := norm_ne_zero_iff.mpr hw
      have hid : ‖F (z i)‖^2*err i=sigma^2*(eta i)^2*‖r (x i)‖^4 := by
        dsimp [err]
        field_simp
      have hM2 : ‖F (z i)‖^2 ≤ M^2 := (sq_le_sq₀ (norm_nonneg _) hM.le).mpr (hFi i)
      have hm := mul_le_mul_of_nonneg_right hM2 (herr0 i)
      rw [hid] at hm
      have hetasq : (eta i)^2 ≤ 1 := pow_le_one₀ (heta i).1.le (heta i).2
      have heta4 : (eta i)^4 ≤ (eta i)^2 := by nlinarith [mul_nonneg (sq_nonneg (eta i)) (sub_nonneg.mpr hetasq)]
      have hlow : sigma^2*(eta i*‖r (x i)‖)^4 ≤ sigma^2*(eta i)^2*‖r (x i)‖^4 := by
        rw [mul_pow]
        calc
          _ = sigma^2*(eta i)^4*‖r (x i)‖^4 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heta4 (sq_nonneg sigma)) (by positivity)
      exact hlow.trans hm
  have hfour : Tendsto (fun i => (eta i*‖r (x i)‖)^4) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => by positivity) (fun i => ?_) (show Tendsto (fun i => M^2/sigma^2*err i) atTop (𝓝 0) by simpa using herr.const_mul (M^2/sigma^2))
    have hs : 0 < sigma^2 := sq_pos_of_pos hσ0
    calc
      _ ≤ (M^2*err i)/sigma^2 := (le_div_iff₀ hs).mpr (by nlinarith [hbound i])
      _ = _ := by ring
  have hsq : Tendsto (fun i => (eta i*‖r (x i)‖)^2) atTop (𝓝 0) := by
    apply root_limit (fun i => sq_nonneg _)
    convert hfour using 1
    ext i
    ring
  exact root_limit (fun i => mul_nonneg (heta i).1.le (norm_nonneg _)) hsq

private theorem residual_lb {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (x : EuclideanSpace ℝ (Fin n)) (hx : x∈C) :
    ‖SolodovSvaiterVI.Alg21.residual F C x‖^2 ≤ ⟪F x,SolodovSvaiterVI.Alg21.residual F C x⟫_ℝ := by
  have hp := (proj_spec C ⟨x,hx⟩ hCc hCcv (x-F x)).2 x hx
  have he : x-F x-projOnto C (x-F x)=SolodovSvaiterVI.Alg21.residual F C x-F x := by
    unfold SolodovSvaiterVI.Alg21.residual
    module
  rw [he] at hp
  change ⟪SolodovSvaiterVI.Alg21.residual F C x-F x,SolodovSvaiterVI.Alg21.residual F C x⟫_ℝ ≤ 0 at hp
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hp
  linarith

private theorem residual_zero_sol {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCne : C.Nonempty) (hCc : IsClosed C) (hCcv : Convex ℝ C) (x : EuclideanSpace ℝ (Fin n))
    (hr : SolodovSvaiterVI.Alg21.residual F C x=0) : x∈viSol F C := by
  have hp := proj_spec C hCne hCc hCcv (x-F x)
  have he : projOnto C (x-F x)=x := (sub_eq_zero.mp hr).symm
  rw [he] at hp
  refine ⟨hp.1,?_⟩
  intro y hy
  have hh := hp.2 y hy
  have hid : x-F x-x=-(F x) := by module
  rw [hid,inner_neg_left] at hh
  linarith

private theorem cluster_solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCc : IsClosed C) (hCcv : Convex ℝ C) (hF : Continuous F) (hS : (viSol F C).Nonempty)
    (h12 : SatisfiesCond12 F C) (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1)
    (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k)
    (l : EuclideanSpace ℝ (Fin n)) (hl : MapClusterPt l atTop x) : l∈viSol F C := by
  obtain ⟨u,hu,hxu⟩ := hl.tendsto_subseq
  have hmem := run_members F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun
  have hlC : l∈C := hCc.mem_of_tendsto hxu (Eventually.of_forall (fun j => hmem (u j)))
  have hCne : C.Nonempty := ⟨l,hlC⟩
  apply residual_zero_sol F C hCne hCc hCcv l
  by_contra hr
  let r := SolodovSvaiterVI.Alg21.residual F C
  let eta (j : ℕ) := gamma^(k (u j))
  have hrc : Continuous r := continuous_id.sub ((proj_continuous C hCne hCc hCcv).comp (continuous_id.sub hF))
  have hrt : Tendsto (fun j => r (x (u j))) atTop (𝓝 (r l)) := hrc.continuousAt.tendsto.comp hxu
  have hnorm := hrt.norm
  have hn : ‖r l‖≠0 := norm_ne_zero_iff.mpr hr
  have hnz : ∀ᶠ j in atTop, ‖r (x (u j))‖≠0 := hnorm.eventually_ne hn
  have hprod : Tendsto (fun j => eta j*‖r (x (u j))‖) atTop (𝓝 0) :=
    (eta_residual_limit F C hCc hCcv hF hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun).comp hu.tendsto_atTop
  have het : Tendsto eta atTop (𝓝 0) := by
    have hh := hprod.div hnorm hn
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [hnz] with j hj
    exact mul_div_cancel_right₀ _ hj
  have hkpos : ∀ᶠ j in atTop, 0 < k (u j) := by
    filter_upwards [het.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with j hj
    by_contra hh
    have hk : k (u j)=0 := by omega
    simp [eta,hk] at hj
  have hprev : Tendsto (fun j => x (u j)-(eta j/gamma)•r (x (u j))) atTop (𝓝 l) := by
    have hh := hxu.sub ((het.div_const gamma).smul hrt)
    simpa using hh
  have hfail : ∀ᶠ j in atTop,
      ⟪F (x (u j)-(eta j/gamma)•r (x (u j))),r (x (u j))⟫_ℝ ≤ sigma*‖r (x (u j))‖^2 := by
    filter_upwards [hkpos,hnz] with j hj hnzj
    have hrj : SolodovSvaiterVI.Alg21.residual F C (x (u j))≠0 := norm_ne_zero_iff.mp hnzj
    have hh := ((hrun.2 (u j)).2 hrj).1.2 (k (u j)-1) (by omega)
    have he : gamma^(k (u j)-1)=eta j/gamma := by
      have hk : k (u j)=(k (u j)-1)+1 := by omega
      dsimp [eta]
      rw [hk,pow_succ]
      exact (mul_div_cancel_right₀ _ (ne_of_gt hγ0)).symm
    change ¬ sigma*‖r (x (u j))‖^2 ≤ ⟪F (x (u j)-gamma^(k (u j)-1)•r (x (u j))),r (x (u j))⟫_ℝ at hh
    rw [he] at hh
    exact (lt_of_not_ge hh).le
  have hlim := le_of_tendsto_of_tendsto ((hF.continuousAt.tendsto.comp hprev).inner hrt)
    (hnorm.pow 2 |>.const_mul sigma) hfail
  have hlower := residual_lb F C hCc hCcv l hlC
  change ‖r l‖^2 ≤ ⟪F l,r l⟫_ℝ at hlower
  have hp : 0 < (1-sigma)*‖r l‖^2 := mul_pos (by linarith) (sq_pos_of_ne_zero hn)
  nlinarith


theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ℕ) (hrun : IsAlg21Run F C gamma sigma x k) :
    ∃ xs ∈ viSol F C, Filter.Tendsto x Filter.atTop (nhds xs) := by
  obtain ⟨a,ha⟩ := hS
  have hS : (viSol F C).Nonempty := ⟨a,ha⟩
  have hm := run_fejer F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun a ha
  have hxB (i : ℕ) : x i∈Metric.closedBall a ‖x 0-a‖ := by
    change dist (x i) a ≤ ‖x 0-a‖
    rw [dist_eq_norm]
    exact hm (Nat.zero_le i)
  have hc := isCompact_closedBall a ‖x 0-a‖
  obtain ⟨l,hlB,hl⟩ := hc.exists_mapClusterPt (f := atTop) (u := x)
    (Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Eventually.of_forall hxB)))
  have hlS := cluster_solution F C hCc hCcv hF hS h12 gamma sigma hγ0 hγ1 hσ0 hσ1 x k hrun l hl
  refine ⟨l,hlS,?_⟩
  have hml := run_fejer F C hCc hCcv hS h12 gamma sigma hγ0 hγ1 hσ0 x k hrun l hlS
  have hb : BddBelow (Set.range (fun i => ‖x i-l‖)) := ⟨0,by rintro _ ⟨i,rfl⟩; exact norm_nonneg _⟩
  have ht := tendsto_atTop_ciInf hml hb
  obtain ⟨u,hu,hxu⟩ := hl.tendsto_subseq
  have hzero : Tendsto (fun j => ‖x (u j)-l‖) atTop (𝓝 0) := by
    simpa using (hxu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => l) atTop (𝓝 l))).norm
  have he := tendsto_nhds_unique (ht.comp hu.tendsto_atTop) hzero
  rw [he] at ht
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using ht

