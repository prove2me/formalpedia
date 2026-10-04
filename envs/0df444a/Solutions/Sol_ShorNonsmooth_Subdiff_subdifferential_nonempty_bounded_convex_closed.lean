-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.subdifferential_nonempty_bounded_convex_closed
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T06:48:52.695539+00:00
-- url     : https://prove2.me/submissions/6ccd94b3-5610-457c-a9d3-9b817261410b

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential


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


open ShorNonsmooth.Subdiff

theorem solution {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M) :
    (subdifferential M f x₀).Nonempty ∧ Bornology.IsBounded (subdifferential M f x₀) ∧
      Convex ℝ (subdifferential M f x₀) ∧ IsClosed (subdifferential M f x₀) :=
  shor_geometry_complete M f hf x₀ hx₀

#print axioms solution
