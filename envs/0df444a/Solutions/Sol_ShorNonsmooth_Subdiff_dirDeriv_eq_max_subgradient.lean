-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.dirDeriv_eq_max_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T07:14:48.205082+00:00
-- url     : https://prove2.me/submissions/84359a7f-44f9-4344-8daa-424cea7c6f8f

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv


namespace ShorNonsmooth.Subdiff
open Set
open scoped RealInnerProductSpace

noncomputable section

theorem shor_closed {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    IsClosed (subdifferential M f x₀) := by
  have he : subdifferential M f x₀=
      ⋂ x : EuclideanSpace ℝ (Fin n), ⋂ (_ : x ∈ M),
        {g | inner ℝ g (x-x₀) ≤ f x-f x₀} := by
    ext g; simp [subdifferential,IsSubgradient]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

theorem shor_convex {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (subdifferential M f x₀) := by
  intro g hg h hh a b ha hb hab
  intro x hx
  have hgx := hg x hx
  have hhx := hh x hx
  change inner ℝ (a • g+b • h) (x-x₀) ≤ f x-f x₀
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
  calc a*inner ℝ g (x-x₀)+b*inner ℝ h (x-x₀)
      ≤ a*(f x-f x₀)+b*(f x-f x₀) :=
        add_le_add (mul_le_mul_of_nonneg_left hgx ha) (mul_le_mul_of_nonneg_left hhx hb)
    _ = f x-f x₀ := by rw [← add_mul,hab,one_mul]

theorem shor_univ_nonempty {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ univ f) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (subdifferential univ f x₀).Nonempty := by
  let E := EuclideanSpace ℝ (Fin n)
  let epi : Set (E × ℝ) := {p | f p.1 < p.2}
  have hc : Convex ℝ epi := by
    simpa only [mem_univ,true_and] using hf.convex_strict_epigraph
  have hfcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have ho : IsOpen epi := isOpen_lt (hfcont.comp continuous_fst) continuous_snd
  have hp : (x₀,f x₀) ∉ epi := by
    change ¬ f x₀ < f x₀
    exact lt_irrefl _
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open hc ho hp
  let a : ℝ := l (0,1)
  have hsplit : ∀ (x : E) (t : ℝ), l (x,t)=l (x,0)+t*a := by
    intro x t
    have he : (x,t)=(x,0)+t • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have ha : 0 < a := by
    have h := hl (x₀,f x₀+1) (by dsimp [epi]; linarith)
    rw [hsplit x₀ (f x₀),hsplit x₀ (f x₀+1)] at h
    linarith
  have hbound : ∀ x : E, l (x₀,f x₀) ≤ l (x,f x) := by
    intro x
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hl (x,f x+ε/a) (by dsimp [epi]; exact lt_add_of_pos_right _ (div_pos hε ha))
    rw [hsplit x₀ (f x₀),hsplit x (f x+ε/a)] at h
    rw [hsplit x₀ (f x₀),hsplit x (f x)]
    have he : a*(ε/a)=ε := by field_simp
    nlinarith
  let lx : E →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let g : E := (-a⁻¹) • (InnerProductSpace.toDual ℝ E).symm lx
  refine ⟨g,?_⟩
  intro x _
  have hx := hbound x
  rw [hsplit x₀ (f x₀),hsplit x (f x)] at hx
  have hi : a * inner ℝ g (x-x₀)=-(l (x,0)-l (x₀,0)) := by
    simp only [g,real_inner_smul_left,InnerProductSpace.toDual_symm_apply,
      lx,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,map_sub]
    field_simp
  change inner ℝ g (x-x₀) ≤ f x-f x₀
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith


theorem shor_open_nonempty {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsOpen M) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) :
    (subdifferential M f x₀).Nonempty := by
  let E := EuclideanSpace ℝ (Fin n)
  let epi : Set (E × ℝ) := {p | p.1 ∈ M ∧ f p.1 < p.2}
  have hc : Convex ℝ epi := by
    exact hf.convex_strict_epigraph
  have ho : IsOpen epi := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hfAt : ContinuousAt f p.1 := (hf.continuousOn hM p.1 hp.1).continuousAt
      (hM.mem_nhds hp.1)
    have hfprod : ContinuousAt (fun q : E × ℝ => f q.1) p :=
      hfAt.comp continuous_fst.continuousAt
    have hm : {q : E × ℝ | q.1 ∈ M} ∈ nhds p :=
      continuous_fst.continuousAt (hM.mem_nhds hp.1)
    have ht := hfprod.eventually_lt continuous_snd.continuousAt hp.2
    filter_upwards [hm,ht] with q hq1 hq2
    exact ⟨hq1,hq2⟩
  have hp : (x₀,f x₀) ∉ epi := by
    change ¬ (x₀ ∈ M ∧ f x₀ < f x₀)
    simp
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open hc ho hp
  let a : ℝ := l (0,1)
  have hsplit : ∀ (x : E) (t : ℝ), l (x,t)=l (x,0)+t*a := by
    intro x t
    have he : (x,t)=(x,0)+t • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have ha : 0 < a := by
    have h := hl (x₀,f x₀+1) (by exact ⟨hx₀,by linarith⟩)
    rw [hsplit x₀ (f x₀),hsplit x₀ (f x₀+1)] at h
    linarith
  have hbound : ∀ x : E, x ∈ M → l (x₀,f x₀) ≤ l (x,f x) := by
    intro x hx
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hl (x,f x+ε/a) (by exact ⟨hx,lt_add_of_pos_right _ (div_pos hε ha)⟩)
    rw [hsplit x₀ (f x₀),hsplit x (f x+ε/a)] at h
    rw [hsplit x₀ (f x₀),hsplit x (f x)]
    have he : a*(ε/a)=ε := by field_simp
    nlinarith
  let lx : E →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let g : E := (-a⁻¹) • (InnerProductSpace.toDual ℝ E).symm lx
  refine ⟨g,?_⟩
  intro x hxm
  have hx := hbound x hxm
  rw [hsplit x₀ (f x₀),hsplit x (f x)] at hx
  have hi : a * inner ℝ g (x-x₀)=-(l (x,0)-l (x₀,0)) := by
    simp only [g,real_inner_smul_left,InnerProductSpace.toDual_symm_apply,
      lx,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,map_sub]
    field_simp
  change inner ℝ g (x-x₀) ≤ f x-f x₀
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith


theorem shor_domain_nonempty {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    (subdifferential M f x₀).Nonempty := by
  obtain ⟨g,hg⟩ := shor_open_nonempty (interior M) isOpen_interior f
    (hf.subset interior_subset hf.1.interior) x₀ hx₀
  refine ⟨g,?_⟩
  intro x hx
  have hy : (1/2 : ℝ) • x₀+(1/2 : ℝ) • x ∈ interior M :=
    hf.1.combo_interior_self_mem_interior hx₀ hx (by norm_num) (by norm_num) (by norm_num)
  have hsupport := hg _ hy
  have hcvx := hf.2 (interior_subset hx₀) hx (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hi : inner ℝ g ((1/2 : ℝ) • x₀+(1/2 : ℝ) • x-x₀)=
      (1/2 : ℝ)*inner ℝ g (x-x₀) := by
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right]
    ring
  rw [hi] at hsupport
  change inner ℝ g (x-x₀) ≤ f x-f x₀
  norm_num only [smul_eq_mul] at hcvx
  linarith

end
end ShorNonsmooth.Subdiff



namespace ShorNonsmooth.Subdiff
open Set
open scoped Topology RealInnerProductSpace

noncomputable section

theorem shor_bounded {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    Bornology.IsBounded (subdifferential M f x₀) := by
  obtain ⟨K,t,ht,hLip⟩ := hf.locallyLipschitzOn_interior hx₀
  have hM : interior M ∈ nhds x₀ := isOpen_interior.mem_nhds hx₀
  rw [nhdsWithin_eq_nhds.mpr hM] at ht
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hM)
  have hx₀t : x₀ ∈ t := (hball (by simp [hε])).1
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(K : ℝ),?_⟩
  intro g hg
  by_cases hz : ‖g‖=0
  · simp [hz]
  have hq : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hz)
  let c : ℝ := ε/(2*‖g‖)
  have hc : 0 < c := by dsimp [c]; positivity
  let y := x₀+c • g
  have hyminus : y-x₀=c • g := by dsimp [y]; abel
  have he : c*‖g‖=ε/2 := by dsimp [c]; field_simp
  have hynorm : ‖y-x₀‖=c*‖g‖ := by
    rw [hyminus,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hyball : y ∈ Metric.ball x₀ ε := by
    rw [Metric.mem_ball,dist_eq_norm,hynorm,he]
    linarith
  obtain ⟨hyt,hyM⟩ := hball hyball
  have hsupport := hg y (interior_subset hyM)
  change inner ℝ g (y-x₀) ≤ f y-f x₀ at hsupport
  rw [hyminus,real_inner_smul_right,real_inner_self_eq_norm_sq] at hsupport
  have hdist := hLip.dist_le_mul y hyt x₀ hx₀t
  rw [Real.dist_eq,dist_eq_norm,hynorm] at hdist
  have hineq : c*‖g‖^2 ≤ (K : ℝ)*(c*‖g‖) :=
    hsupport.trans ((le_abs_self _).trans hdist)
  have hm : (c*‖g‖)*‖g‖ ≤ (c*‖g‖)*(K : ℝ) := by
    convert hineq using 1 <;> ring
  exact le_of_mul_le_mul_left hm (mul_pos hc hq)

theorem shor_geometry_complete {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    (subdifferential M f x₀).Nonempty ∧ Bornology.IsBounded (subdifferential M f x₀) ∧
      Convex ℝ (subdifferential M f x₀) ∧ IsClosed (subdifferential M f x₀) :=
  ⟨shor_domain_nonempty M f hf x₀ hx₀,shor_bounded M f hf x₀ hx₀,
    shor_convex M f x₀,shor_closed M f x₀⟩

end
end ShorNonsmooth.Subdiff



namespace ShorNonsmooth.Subdiff
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

theorem shor_line_combo {n : ℕ} (x v : EuclideanSpace ℝ (Fin n))
    (a b u w : ℝ) (huw : u+w=1) :
    u • (x+a • v)+w • (x+b • v)=x+(u*a+w*b) • v := by
  rw [smul_add,smul_add,smul_smul,smul_smul]
  calc u • x+(u*a) • v+(w • x+(w*b) • v)
      = (u • x+w • x)+((u*a) • v+(w*b) • v) := by abel
    _ = x+(u*a+w*b) • v := by rw [← add_smul,← add_smul,huw,one_smul]

theorem shor_line_convex_domain {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ ((fun t : ℝ => x+t • v) ⁻¹' M) (fun t : ℝ => f (x+t • v)) := by
  refine ⟨?_,?_⟩
  · intro a ha b hb u w hu hw huw
    change x+(u*a+w*b) • v ∈ M
    rw [← shor_line_combo x v a b u w huw]
    exact hf.1 ha hb hu hw huw
  · intro a ha b hb u w hu hw huw
    have h := hf.2 ha hb hu hw huw
    simpa only [shor_line_combo x v a b u w huw,smul_eq_mul] using h

theorem shor_hasDir_iff_right {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    HasOneSidedDirDeriv f x v d ↔
      HasDerivWithinAt (fun t : ℝ => f (x+t • v)) d (Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0:ℝ) ∉ Ioi 0)]
  rw [slope_fun_def_field]
  simp only [HasOneSidedDirDeriv,sub_zero,zero_smul,add_zero]

theorem shor_direction_exists {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior M)
    (v : EuclideanSpace ℝ (Fin n)) : ∃ d,HasOneSidedDirDeriv f x v d := by
  let S := (fun t : ℝ => x+t • v) ⁻¹' M
  have hS : (0:ℝ) ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    have hm : M ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
    have h := hc.continuousAt (x:=0) (by simpa using hm)
    exact h
  have hc := shor_line_convex_domain M f hf x v
  exact ⟨_,(shor_hasDir_iff_right f x v _).mpr
    (hc.hasDerivWithinAt_rightDeriv_of_mem_interior hS)⟩

theorem shor_pair_le_direction {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ interior M) (v g : EuclideanSpace ℝ (Fin n))
    (hg : g ∈ subdifferential M f x) (d : ℝ) (hd : HasOneSidedDirDeriv f x v d) :
    inner ℝ g v ≤ d := by
  apply ge_of_tendsto hd
  have hm : ∀ᶠ t : ℝ in 𝓝 0,x+t • v ∈ M := by
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    exact hc.continuousAt (x:=0) (by simpa using mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htp
  have htpos : 0<t := htp
  have h := hg (x+t • v) ht
  change inner ℝ g (x+t • v-x) ≤ f (x+t • v)-f x at h
  have he : x+t • v-x=t • v := by abel
  rw [he,real_inner_smul_right] at h
  exact (le_div_iff₀ htpos).mpr (by nlinarith)

end
end ShorNonsmooth.Subdiff


namespace ShorNonsmooth.Subdiff
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

theorem shor_uniform_bound {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    ∃ K : ℝ, ∃ U ∈ 𝓝 x₀, U ⊆ interior M ∧
      ∀ y ∈ U, ∀ g ∈ subdifferential M f y, ‖g‖ ≤ K := by
  obtain ⟨K,t,ht,hLip⟩ := hf.locallyLipschitzOn_interior hx₀
  have hM : interior M ∈ nhds x₀ := isOpen_interior.mem_nhds hx₀
  rw [nhdsWithin_eq_nhds.mpr hM] at ht
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hM)
  have hsmall : Metric.ball x₀ (ε/2) ⊆ Metric.ball x₀ ε := by
    apply Metric.ball_subset_ball
    linarith
  refine ⟨(K:ℝ),Metric.ball x₀ (ε/2),Metric.ball_mem_nhds x₀ (by linarith),
    (fun y hy => (hball (hsmall hy)).2),?_⟩
  intro y hy g hg
  have hyt : y ∈ t := (hball (hsmall hy)).1
  by_cases hz : ‖g‖=0
  · simp only [hz]
    exact K.coe_nonneg
  have hq : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hz)
  let c : ℝ := ε/(2*‖g‖)
  have hc : 0<c := by dsimp [c]; positivity
  let z := y+c • g
  have hzminus : z-y=c • g := by dsimp [z]; abel
  have he : c*‖g‖=ε/2 := by dsimp [c]; field_simp
  have hznorm : ‖z-y‖=c*‖g‖ := by
    rw [hzminus,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hzball : z ∈ Metric.ball x₀ ε := by
    rw [Metric.mem_ball]
    calc dist z x₀ ≤ dist z y+dist y x₀ := dist_triangle _ _ _
      _ < ε/2+ε/2 := by rw [dist_eq_norm,hznorm,he]; exact add_lt_add_right (Metric.mem_ball.mp hy) _
      _ = ε := by ring
  obtain ⟨hzt,hzM⟩ := hball hzball
  have hs := hg z (interior_subset hzM)
  change inner ℝ g (z-y) ≤ f z-f y at hs
  rw [hzminus,real_inner_smul_right,real_inner_self_eq_norm_sq] at hs
  have hdist := hLip.dist_le_mul z hzt y hyt
  rw [Real.dist_eq,dist_eq_norm,hznorm] at hdist
  have hineq : c*‖g‖^2 ≤ (K:ℝ)*(c*‖g‖) := hs.trans ((le_abs_self _).trans hdist)
  have hm : (c*‖g‖)*‖g‖ ≤ (c*‖g‖)*(K:ℝ) := by convert hineq using 1 <;> ring
  exact le_of_mul_le_mul_left hm (mul_pos hc hq)

end
end ShorNonsmooth.Subdiff


namespace ShorNonsmooth.Subdiff
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

theorem shor_directional_complete {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior M)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ d, HasOneSidedDirDeriv f x v d ∧
      IsGreatest ((fun g => inner ℝ g v) '' subdifferential M f x) d := by
  classical
  obtain ⟨d,hd⟩ := shor_direction_exists M f hf x hx v
  obtain ⟨K,U,hU,hUM,hbound⟩ := shor_uniform_bound M f hf x hx
  let P : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x+t • v
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hPi : ∀ᶠ t in 𝓝 0,P t ∈ interior M := by
    exact hP.continuousAt (x:=0) (by simpa [P] using isOpen_interior.mem_nhds hx)
  have hPU : ∀ᶠ t in 𝓝 0,P t ∈ U := by
    exact hP.continuousAt (x:=0) (by simpa [P] using hU)
  let G : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    if ht : P t ∈ interior M then (shor_domain_nonempty M f hf (P t) ht).choose else 0
  have hG : ∀ᶠ t in 𝓝 0,G t ∈ subdifferential M f (P t) := by
    filter_upwards [hPi] with t ht
    dsimp [G]
    rw [dif_pos ht]
    exact (shor_domain_nonempty M f hf (P t) ht).choose_spec
  have hK : ∀ᶠ t in 𝓝 0,‖G t‖ ≤ K := by
    filter_upwards [hPU,hG] with t ht hg
    exact hbound (P t) ht (G t) hg
  let T : ℕ → ℝ := fun i => 1/((i:ℝ)+1)
  have hT0 : Tendsto T atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hTpos : ∀ i,0<T i := by intro i; dsimp [T]; positivity
  have hTright : Tendsto T atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT0,Eventually.of_forall hTpos⟩
  have hseq : ∀ᶠ i in atTop,G (T i) ∈ Metric.closedBall 0 K := by
    filter_upwards [hT0 hK] with i hi
    simpa [Metric.mem_closedBall,dist_eq_norm] using hi
  obtain ⟨g,hgball,φ,hφ,hg_lim⟩ := (isCompact_closedBall (0:EuclideanSpace ℝ (Fin n)) K).tendsto_subseq' hseq.frequently
  have hφtop := hφ.tendsto_atTop
  have htime : Tendsto (fun i => T (φ i)) atTop (𝓝 (0:ℝ)) := hT0.comp hφtop
  have htimer : Tendsto (fun i => T (φ i)) atTop (𝓝[>] (0:ℝ)) := hTright.comp hφtop
  have hpoint : Tendsto (fun i => P (T (φ i))) atTop (𝓝 x) := by
    simpa [P] using (tendsto_const_nhds.add (htime.smul_const v))
  have hfcont : ContinuousAt f x :=
    ((hf.subset interior_subset hf.1.interior).continuousOn isOpen_interior x hx).continuousAt (isOpen_interior.mem_nhds hx)
  have hfun : Tendsto (fun i => f (P (T (φ i)))) atTop (𝓝 (f x)) := hfcont.tendsto.comp hpoint
  have hsub : ∀ᶠ i in atTop,G (T (φ i)) ∈ subdifferential M f (P (T (φ i))) := htime hG
  have hgx : g ∈ subdifferential M f x := by
    intro y hy
    have hleft : Tendsto (fun i => inner ℝ (G (T (φ i))) (y-P (T (φ i))))
        atTop (𝓝 (inner ℝ g (y-x))) := hg_lim.inner (tendsto_const_nhds.sub hpoint)
    have hright : Tendsto (fun i => f y-f (P (T (φ i)))) atTop (𝓝 (f y-f x)) :=
      tendsto_const_nhds.sub hfun
    exact le_of_tendsto_of_tendsto hleft hright (hsub.mono fun i hi => hi y hy)
  have hupper : d ≤ inner ℝ g v := by
    have hquot := hd.comp htimer
    have hip : Tendsto (fun i => inner ℝ (G (T (φ i))) v) atTop (𝓝 (inner ℝ g v)) :=
      hg_lim.inner tendsto_const_nhds
    apply le_of_tendsto_of_tendsto hquot hip
    filter_upwards [hsub] with i hi
    have h := hi x (interior_subset hx)
    have he : x-P (T (φ i))=-(T (φ i)) • v := by dsimp [P]; module
    change inner ℝ (G (T (φ i))) (x-P (T (φ i))) ≤ f x-f (P (T (φ i))) at h
    rw [he,real_inner_smul_right] at h
    apply (div_le_iff₀ (hTpos (φ i))).mpr
    change f (P (T (φ i)))-f x ≤ _
    nlinarith
  have hlow := shor_pair_le_direction M f x hx v g hgx d hd
  have he : inner ℝ g v=d := le_antisymm hlow hupper
  refine ⟨d,hd,⟨⟨g,hgx,he⟩,?_⟩⟩
  rintro z ⟨g',hg',rfl⟩
  exact shor_pair_le_direction M f x hx v g' hg' d hd

end
end ShorNonsmooth.Subdiff
noncomputable section
open ShorNonsmooth.Subdiff
theorem solution {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M)
    (η : EuclideanSpace ℝ (Fin n)) :
    ∃ d : ℝ, HasOneSidedDirDeriv f x₀ η d ∧
      IsGreatest ((fun g => inner ℝ g η) '' subdifferential M f x₀) d :=
  shor_directional_complete M f hf x₀ hx₀ η
end
#print axioms solution
