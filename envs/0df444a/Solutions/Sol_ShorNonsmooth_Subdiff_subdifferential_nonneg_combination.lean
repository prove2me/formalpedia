-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.subdifferential_nonneg_combination
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T07:00:19.848071+00:00
-- url     : https://prove2.me/submissions/5fe5220d-5096-4cf4-9302-e0d6b005cdc8

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

theorem shor_binary_sum {n : ℕ} (F G : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ univ F) (hG : ConvexOn ℝ univ G)
    (x₀ g : EuclideanSpace ℝ (Fin n))
    (hg : g ∈ subdifferential univ (fun x => F x+G x) x₀) :
    ∃ gF gG, gF ∈ subdifferential univ F x₀ ∧ gG ∈ subdifferential univ G x₀ ∧ g=gF+gG := by
  let E := EuclideanSpace ℝ (Fin n)
  let Q : E → ℝ := fun x => F x₀+G x₀+inner ℝ g (x-x₀)-G x
  have hlin : ConcaveOn ℝ univ (fun x : E => F x₀+G x₀+inner ℝ g (x-x₀)) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right,smul_eq_mul]
    have he := congrArg (fun c : ℝ => c*(F x₀+G x₀-inner ℝ g x₀)) hab
    nlinarith
  have hQ : ConcaveOn ℝ univ Q := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have hL := hlin.2 hx hy ha hb hab
    have hC := hG.2 hx hy ha hb hab
    change a*Q x+b*Q y ≤ Q (a • x+b • y)
    dsimp [Q]
    simp only [smul_eq_mul] at hL hC
    nlinarith
  have hFc : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  let s : Set (E × ℝ) := {p | F p.1<p.2}
  let t : Set (E × ℝ) := {p | p.2<Q p.1}
  have hsc : Convex ℝ s := by simpa only [mem_univ,true_and] using hF.convex_strict_epigraph
  have htc : Convex ℝ t := by simpa only [mem_univ,true_and] using hQ.convex_strict_hypograph
  have hso : IsOpen s := isOpen_lt (hFc.comp continuous_fst) continuous_snd
  have hto : IsOpen t := isOpen_lt continuous_snd (hQc.comp continuous_fst)
  have hdisj : Disjoint s t := by
    apply disjoint_left.mpr
    intro p hp hpt
    have he := hg p.1 (mem_univ _)
    change inner ℝ g (p.1-x₀) ≤ (F p.1+G p.1)-(F x₀+G x₀) at he
    dsimp [s,t,Q] at hp hpt
    linarith
  obtain ⟨l,u,hs,ht⟩ := geometric_hahn_banach_open_open hsc hso htc hto hdisj
  let a : ℝ := l (0,1)
  have hsplit : ∀ (x : E) (r : ℝ), l (x,r)=l (x,0)+r*a := by
    intro x r
    have he : (x,r)=(x,0)+r • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]; rfl
  have hQ0 : Q x₀=F x₀ := by simp [Q]
  have ha : a<0 := by
    have h1 := hs (x₀,F x₀+1) (by change F x₀<F x₀+1; linarith)
    have h2 := ht (x₀,F x₀-1) (by change F x₀-1<Q x₀; rw [hQ0]; linarith)
    rw [hsplit x₀ (F x₀+1)] at h1
    rw [hsplit x₀ (F x₀-1)] at h2
    linarith
  have hbF : ∀ x : E, l (x,F x) ≤ u := by
    intro x; apply le_of_forall_pos_le_add
    intro ε hε
    have h := hs (x,F x+ε/(-a)) (by change F x<F x+ε/(-a); linarith [div_pos hε (neg_pos.mpr ha)])
    rw [hsplit x (F x+ε/(-a))] at h
    rw [hsplit x (F x)]
    have he : a*(ε/(-a))=-ε := by field_simp [ne_of_lt ha]
    nlinarith
  have hbQ : ∀ x : E, u ≤ l (x,Q x) := by
    intro x; apply le_of_forall_pos_le_add
    intro ε hε
    have h := ht (x,Q x-ε/(-a)) (by change Q x-ε/(-a)<Q x; linarith [div_pos hε (neg_pos.mpr ha)])
    rw [hsplit x (Q x-ε/(-a))] at h
    rw [hsplit x (Q x)]
    have he : a*(ε/(-a))=-ε := by field_simp [ne_of_lt ha]
    nlinarith
  have hu : u=l (x₀,F x₀) := by
    have h1 := hbF x₀
    have h2 := hbQ x₀
    rw [hQ0] at h2
    exact le_antisymm h2 h1
  let lx : E →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let gF : E := (-a⁻¹) • (InnerProductSpace.toDual ℝ E).symm lx
  have hi : ∀ x : E, a*inner ℝ gF (x-x₀)=-(l (x,0)-l (x₀,0)) := by
    intro x
    simp only [gF,real_inner_smul_left,InnerProductSpace.toDual_symm_apply,
      lx,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,map_sub]
    field_simp [ne_of_lt ha]
  have hsubF : gF ∈ subdifferential univ F x₀ := by
    intro x _
    have hx := hbF x
    rw [hu,hsplit x (F x),hsplit x₀ (F x₀)] at hx
    change inner ℝ gF (x-x₀) ≤ F x-F x₀
    apply (mul_le_mul_iff_right₀ (neg_pos.mpr ha)).mp
    nlinarith [hi x]
  have hsubG : g-gF ∈ subdifferential univ G x₀ := by
    intro x _
    have hx := hbQ x
    rw [hu,hsplit x (Q x),hsplit x₀ (F x₀)] at hx
    dsimp [Q] at hx
    change inner ℝ (g-gF) (x-x₀) ≤ G x-G x₀
    rw [inner_sub_left]
    apply (mul_le_mul_iff_right₀ (neg_pos.mpr ha)).mp
    nlinarith [hi x]
  exact ⟨gF,g-gF,hsubF,hsubG,by abel⟩

end
end ShorNonsmooth.Subdiff



namespace ShorNonsmooth.Subdiff
open Set
open scoped RealInnerProductSpace
noncomputable section

theorem shor_const_subgrad {n : ℕ} (c : ℝ) (x₀ g : EuclideanSpace ℝ (Fin n)) :
    g ∈ subdifferential univ (fun _ => c) x₀ ↔ g=0 := by
  constructor
  · intro hg
    have h := hg (x₀+g) (mem_univ _)
    change inner ℝ g (x₀+g-x₀) ≤ c-c at h
    have he : x₀+g-x₀=g := by abel
    rw [he,real_inner_self_eq_norm_sq] at h
    have hz : ‖g‖=0 := by nlinarith [norm_nonneg g]
    exact norm_eq_zero.mp hz
  · rintro rfl
    intro x _
    simp

theorem shor_positive_unscale {n : ℕ} (a : ℝ) (ha : 0<a)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ g : EuclideanSpace ℝ (Fin n))
    (hg : g ∈ subdifferential univ (fun x => a*f x) x₀) :
    a⁻¹ • g ∈ subdifferential univ f x₀ := by
  intro x hx
  have h := hg x hx
  change inner ℝ (a⁻¹ • g) (x-x₀) ≤ f x-f x₀
  rw [real_inner_smul_left]
  apply (mul_le_mul_iff_right₀ ha).mp
  have he : a*(a⁻¹*inner ℝ g (x-x₀))=inner ℝ g (x-x₀) := by field_simp
  rw [he]
  change inner ℝ g (x-x₀) ≤ a*(f x-f x₀)
  change inner ℝ g (x-x₀) ≤ a*f x-a*f x₀ at h
  nlinarith

theorem shor_sum_convex {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i,0≤a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i,ConvexOn ℝ univ (f i)) :
    ConvexOn ℝ univ (fun x => ∑ i,a i*f i x) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy u v hu hv huv
  change (∑ i,a i*f i (u • x+v • y)) ≤ u*(∑ i,a i*f i x)+v*(∑ i,a i*f i y)
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left ((hf i).2 hx hy hu hv huv) (ha i)
  simp only [smul_eq_mul] at h
  nlinarith

theorem shor_weighted_subgrad {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i,0≤a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (gs : Fin k → EuclideanSpace ℝ (Fin n))
    (hgs : ∀ i,gs i ∈ subdifferential univ (f i) x₀) :
    (∑ i,a i • gs i) ∈ subdifferential univ (fun x => ∑ i,a i*f i x) x₀ := by
  intro x hx
  change inner ℝ (∑ i,a i • gs i) (x-x₀) ≤ (∑ i,a i*f i x)-(∑ i,a i*f i x₀)
  rw [sum_inner,← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [real_inner_smul_left]
  have h := mul_le_mul_of_nonneg_left (hgs i x hx) (ha i)
  nlinarith

theorem shor_sum_decompose {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i,0≤a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i,ConvexOn ℝ univ (f i))
    (x₀ g : EuclideanSpace ℝ (Fin n))
    (hg : g ∈ subdifferential univ (fun x => ∑ i,a i*f i x) x₀) :
    ∃ gs : Fin k → EuclideanSpace ℝ (Fin n),
      (∀ i,gs i ∈ subdifferential univ (f i) x₀) ∧ g=∑ i,a i • gs i := by
  induction k generalizing g with
  | zero =>
    have he : (fun x => ∑ i : Fin 0,a i*f i x)=(fun _ => 0) := by funext x; simp
    rw [he] at hg
    have hz := (shor_const_subgrad 0 x₀ g).mp hg
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,?_⟩
    simpa using hz
  | succ k ih =>
    let aT : Fin k → ℝ := fun i => a i.succ
    let fT : Fin k → EuclideanSpace ℝ (Fin n) → ℝ := fun i => f i.succ
    let FT := fun x => ∑ i : Fin k,aT i*fT i x
    have he : (fun x => ∑ i : Fin (k+1),a i*f i x)=(fun x => a 0*f 0 x+FT x) := by
      funext x; rw [Fin.sum_univ_succ]
    rw [he] at hg
    have hc0 : ConvexOn ℝ univ (fun x => a 0*f 0 x) := by
      simpa only [smul_eq_mul] using ConvexOn.smul (ha 0) (hf 0)
    have hcT : ConvexOn ℝ univ FT := shor_sum_convex aT (fun i => ha i.succ) fT (fun i => hf i.succ)
    obtain ⟨g0,gT,hg0,hgT,hgadd⟩ := shor_binary_sum _ _ hc0 hcT x₀ g hg
    obtain ⟨gsT,hgsT,heT⟩ := ih aT (fun i => ha i.succ) fT (fun i => hf i.succ) gT hgT
    have hhead : ∃ gs0,gs0 ∈ subdifferential univ (f 0) x₀ ∧ a 0 • gs0=g0 := by
      by_cases hz : a 0=0
      · have hfun : (fun x => a 0*f 0 x)=(fun _ => 0) := by simp [hz]
        rw [hfun] at hg0
        have hg0z := (shor_const_subgrad 0 x₀ g0).mp hg0
        obtain ⟨gs0,hgs0⟩ := shor_univ_nonempty (f 0) (hf 0) x₀
        exact ⟨gs0,hgs0,by simp [hz,hg0z]⟩
      · have hp : 0<a 0 := lt_of_le_of_ne (ha 0) (Ne.symm hz)
        refine ⟨(a 0)⁻¹ • g0,shor_positive_unscale _ hp _ x₀ g0 hg0,?_⟩
        rw [smul_smul,mul_inv_cancel₀ hz,one_smul]
    obtain ⟨gs0,hgs0,hgs0eq⟩ := hhead
    refine ⟨Fin.cons gs0 gsT,?_,?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨hgs0,hgsT⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [hgs0eq,hgadd]
      congr 1

theorem shor_sum_rule_complete {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i,0≤a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i,ConvexOn ℝ univ (f i)) :
    ConvexOn ℝ univ (fun x => ∑ i,a i*f i x) ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n),
        subdifferential univ (fun x => ∑ i,a i*f i x) x₀ =
          {g | ∃ gs : Fin k → EuclideanSpace ℝ (Fin n),
            (∀ i,gs i ∈ subdifferential univ (f i) x₀) ∧ g=∑ i,a i • gs i} := by
  refine ⟨shor_sum_convex a ha f hf,?_⟩
  intro x₀
  ext g
  constructor
  · exact shor_sum_decompose a ha f hf x₀ g
  · rintro ⟨gs,hgs,rfl⟩
    exact shor_weighted_subgrad a ha f x₀ gs hgs

end
end ShorNonsmooth.Subdiff

noncomputable section
open ShorNonsmooth.Subdiff

theorem solution {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun x => ∑ i, a i * f i x) ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n),
        subdifferential Set.univ (fun x => ∑ i, a i * f i x) x₀ =
          {g | ∃ gs : Fin k → EuclideanSpace ℝ (Fin n),
            (∀ i, gs i ∈ subdifferential Set.univ (f i) x₀) ∧
            g = ∑ i, a i • gs i} := shor_sum_rule_complete a ha f hf
end
#print axioms solution
