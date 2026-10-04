-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.nonsmooth_penalty_exact
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T20:08:26.040096+00:00
-- url     : https://prove2.me/submissions/1195a852-af60-4376-b2ea-ad5c433a538f

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_PenaltyDual
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

-- Shared checked proof: ValueFnUpper

namespace ShorNonsmooth.Decomposition
open Set
open scoped Topology RealInnerProductSpace
noncomputable section

lemma vf_strict_combo {x y u v a b : ℝ} (hx : x < y) (hu : u < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : a*x+b*u < a*y+b*v := by
  by_cases hz : a=0
  · subst a
    have he : b=1 := by linarith
    simpa [he] using hu
  · have hp : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hp)
      (mul_le_mul_of_nonneg_left hu.le hb)

def vf_upper {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | ∃ x, (∀ i, g i x < p.1 i) ∧ F x-v < p.2}

lemma vf_upper_open {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ) :
    IsOpen (vf_upper F g v) := by
  have he : vf_upper F g v=⋃ x, (⋂ i : Fin n, {p : (Fin n → ℝ) × ℝ | g i x < p.1 i}) ∩
      {p : (Fin n → ℝ) × ℝ | F x-v < p.2} := by
    ext p; simp [vf_upper]
  rw [he]
  apply isOpen_iUnion
  intro x
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (by fun_prop)
  · exact isOpen_lt continuous_const continuous_snd

lemma vf_upper_convex {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (hF : ConvexOn ℝ univ F) (hg : ∀ i, ConvexOn ℝ univ (g i)) :
    Convex ℝ (vf_upper F g v) := by
  rintro p ⟨x,hx,hFx⟩ q ⟨y,hy,hFy⟩ a b ha hb hab
  refine ⟨a • x+b • y,fun i => ?_,?_⟩
  · have h := (hg i).2 (mem_univ x) (mem_univ y) ha hb hab
    have hs := vf_strict_combo (hx i) (hy i) ha hb hab
    change g i (a • x+b • y) < a*p.1 i+b*q.1 i
    simpa only [smul_eq_mul] using h.trans_lt hs
  · have h := hF.2 (mem_univ x) (mem_univ y) ha hb hab
    have hs := vf_strict_combo hFx hFy ha hb hab
    change F (a • x+b • y)-v < a*p.2+b*q.2
    simp only [smul_eq_mul] at h
    have he := congrArg (fun t : ℝ => t*v) hab
    simp only [add_mul,one_mul] at he
    nlinarith

lemma vf_upper_add {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    {p d : (Fin n → ℝ) × ℝ} (hp : p ∈ vf_upper F g v)
    (hd : ∀ i, 0 ≤ d.1 i) (ht : 0 ≤ d.2) : p+d ∈ vf_upper F g v := by
  obtain ⟨x,hx,hFx⟩ := hp
  exact ⟨x,fun i => (hx i).trans_le (le_add_of_nonneg_right (hd i)),
    hFx.trans_le (le_add_of_nonneg_right ht)⟩

lemma vf_split {n : ℕ} (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) (t : ℝ) :
    L (v,t)=(∑ i, L (Pi.single i (1:ℝ),0)*v i)+L (0,1)*t := by
  classical
  have hv : (v,(0:ℝ)) = ∑ i : Fin n, v i • (Pi.single i (1:ℝ),(0:ℝ)) := by
    simp only [Prod.smul_mk,smul_zero,← prod_mk_sum,Finset.sum_const_zero]
    exact congrArg (fun w : Fin n → ℝ => (w,(0:ℝ))) (pi_eq_sum_univ' v)
  have he : (v,t)=(v,0)+t • (0,1) := by ext <;> simp
  rw [he,map_add,map_smul,hv,map_sum]
  simp only [map_smul,smul_eq_mul,mul_comm]

lemma vf_slope_nonneg (q a : ℝ) (h : ∀ t : ℝ, 0 ≤ t → 0 < q+t*a) : 0 ≤ a := by
  by_contra hn
  have ha : a<0 := lt_of_not_ge hn
  have hq : 0<q := by simpa using h 0 (by norm_num)
  let t := (q+1)/(-a)
  have ht : 0 ≤ t := div_nonneg (by linarith) (le_of_lt (neg_pos.mpr ha))
  have he : t*a= -(q+1) := by dsimp [t]; field_simp [ne_of_lt ha] <;> ring
  have hbad := h t ht
  rw [he] at hbad
  linarith

lemma vf_coeff_nonneg {E : Type*} [Zero E] {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (hL : ∀ p ∈ vf_upper F g v, 0 < L p) :
    (∀ i, 0 ≤ L (Pi.single i (1:ℝ),0)) ∧ 0 ≤ L (0,1) := by
  classical
  let p : (Fin n → ℝ) × ℝ := (fun i => g i 0+1,F 0-v+1)
  have hp : p ∈ vf_upper F g v := ⟨0,fun i => by dsimp [p]; linarith,by dsimp [p]; linarith⟩
  constructor
  · intro i
    apply vf_slope_nonneg (L p)
    intro t ht
    have hmem : p+t • (Pi.single i (1:ℝ),0) ∈ vf_upper F g v := by
      apply vf_upper_add F g v hp
      · intro j
        change 0 ≤ t*(Pi.single (M := fun _ => ℝ) i (1:ℝ) j)
        have hs : 0 ≤ Pi.single (M := fun _ => ℝ) i (1:ℝ) j := by
          by_cases hj : j=i <;> simp [hj]
        exact mul_nonneg ht hs
      · simp
    simpa only [map_add,map_smul,smul_eq_mul] using hL _ hmem
  · apply vf_slope_nonneg (L p)
    intro t ht
    have hmem : p+t • (0,1) ∈ vf_upper F g v :=
      vf_upper_add F g v hp (fun _ => by simp) (by simpa using ht)
    simpa only [map_add,map_smul,smul_eq_mul] using hL _ hmem

lemma vf_upper_bound {E : Type*} {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (hL : ∀ p ∈ vf_upper F g v, 0 < L p)
    (hu : ∀ i, 0 ≤ L (Pi.single i (1:ℝ),0)) (ha : 0 < L (0,1)) (x : E) :
    0 ≤ (∑ i, L (Pi.single i (1:ℝ),0)*g i x)+L (0,1)*(F x-v) := by
  let u : Fin n → ℝ := fun i => L (Pi.single i (1:ℝ),0)
  let a : ℝ := L (0,1)
  let K : ℝ := (∑ i, u i)+a
  have hsum : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu i)
  have hK : 0<K := by dsimp [K,a]; linarith
  change 0 ≤ (∑ i, u i*g i x)+a*(F x-v)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/K
  have hδ : 0<δ := div_pos hε hK
  have hp : (fun i => g i x+δ,F x-v+δ) ∈ vf_upper F g v :=
    ⟨x,fun i => lt_add_of_pos_right _ hδ,lt_add_of_pos_right _ hδ⟩
  have h := hL _ hp
  rw [vf_split] at h
  change 0 < (∑ i, u i*(g i x+δ))+a*(F x-v+δ) at h
  have he : (∑ i, u i*(g i x+δ))+a*(F x-v+δ)=
      (∑ i, u i*g i x)+a*(F x-v)+ε := by
    have hk : δ*K=ε := by dsimp [δ]; field_simp [ne_of_gt hK]
    dsimp [K] at hk
    rw [mul_add,Finset.mul_sum] at hk
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    have hcomm : (∑ i, u i*δ)=∑ i, δ*u i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hcomm]
    nlinarith
  rw [he] at h
  exact h.le

lemma vf_partial_convex {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : JointlyConvex F) (x : EuclideanSpace ℝ (Fin l)) :
    ConvexOn ℝ univ (F x) := by
  refine ⟨convex_univ,?_⟩
  intro y hy z hz a b ha hb hab
  have h := hF.2 (mem_univ (x,y)) (mem_univ (x,z)) ha hb hab
  have he : a • x+b • x=x := by rw [← add_smul,hab,one_smul]
  simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,he] using h

end
end ShorNonsmooth.Decomposition

-- Shared checked proof: ValueFnPenaltyBasic

namespace ShorNonsmooth.Decomposition
open Set Filter Topology
noncomputable section

lemma vp_nonneg (p : ℝ → ℝ) (hp : IsPenaltyFunction p) (t : ℝ) : 0≤p t := by
  by_cases ht : t≤0
  · rw [hp.2.1 t ht]
  · exact (hp.2.2 t (lt_of_not_ge ht)).le

lemma vp_monotone (p : ℝ → ℝ) (hp : IsPenaltyFunction p) : Monotone p := by
  intro x y hxy
  by_cases hx : x≤0
  · rw [hp.2.1 x hx]
    exact vp_nonneg p hp y
  have hx0 : 0<x := lt_of_not_ge hx
  rcases eq_or_lt_of_le hxy with he | hlt
  · rw [he]
  have h := hp.1.secant_mono_aux1 (mem_univ (0:ℝ)) (mem_univ y) hx0 hlt
  rw [hp.2.1 0 le_rfl] at h
  simp only [sub_zero,mul_zero,zero_add] at h
  have h2 := mul_le_mul_of_nonneg_right hxy (vp_nonneg p hp y)
  nlinarith

lemma vp_slope_bound (p : ℝ → ℝ) (hp : IsPenaltyFunction p) (c : ℝ)
    (hc : Tendsto (fun t => p t/t) (𝓝[>]0) (𝓝 c)) {t : ℝ} (ht : 0<t) : c*t≤p t := by
  have h : c≤p t/t := by
    apply le_of_tendsto hc
    filter_upwards [Ioo_mem_nhdsGT ht] with z hz
    have hs := hp.1.secant_mono_aux2 (mem_univ (0:ℝ)) (mem_univ t) hz.1 hz.2
    simpa only [hp.2.1 0 le_rfl,sub_zero] using hs
  exact (le_div_iff₀ ht).mp h

lemma vp_zero_on_feasible {N m : ℕ}
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (p : Fin m → ℝ → ℝ) (hp : ∀ i,IsPenaltyFunction (p i))
    {x : EuclideanSpace ℝ (Fin N)} (hx : x∈feasibleSet f) : penalized F f p x=F x := by
  unfold penalized
  have hz : (∑ i,p i (f i x))=0 := Finset.sum_eq_zero (fun i _ => (hp i).2.1 _ (hx i))
  rw [hz,add_zero]

lemma vp_penalty_dual_gap {N m : ℕ}
    (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (p : Fin m → ℝ → ℝ) (hp : ∀ i,IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i,Tendsto (fun t => p i t/t) (𝓝[>]0) (𝓝 (c i)))
    (U : Fin m → ℝ) (hU : ∀ i,0≤U i) (hUc : ∀ i,U i<c i)
    (x : EuclideanSpace ℝ (Fin N)) :
    (∑ i,U i*f i x) ≤ ∑ i,p i (f i x) ∧
    (x∉feasibleSet f → (∑ i,U i*f i x)<∑ i,p i (f i x)) := by
  have hle : ∀ i,U i*f i x≤p i (f i x) := by
    intro i
    by_cases ht : f i x≤0
    · rw [(hp i).2.1 _ ht]
      exact mul_nonpos_of_nonneg_of_nonpos (hU i) ht
    · have ht0 : 0<f i x := lt_of_not_ge ht
      exact (mul_le_mul_of_nonneg_right (hUc i).le ht0.le).trans
        (vp_slope_bound (p i) (hp i) (c i) (hc i) ht0)
  refine ⟨Finset.sum_le_sum (fun i _ => hle i),?_⟩
  intro hx
  have hbad : ∃ i,0<f i x := by
    by_contra hn
    apply hx
    intro i
    exact le_of_not_gt (fun hi => hn ⟨i,hi⟩)
  obtain ⟨i,hi⟩ := hbad
  apply Finset.sum_lt_sum (fun j _ => hle j)
  refine ⟨i,Finset.mem_univ i,?_⟩
  exact (mul_lt_mul_of_pos_right (hUc i) hi).trans_le
    (vp_slope_bound (p i) (hp i) (c i) (hc i) hi)

end
end ShorNonsmooth.Decomposition

-- Shared checked proof: ValueFnPenaltyNecessity

namespace ShorNonsmooth.Decomposition
open Set Filter Topology
noncomputable section

lemma vp_penalty_hypograph_convex {m : ℕ} (p : Fin m → ℝ → ℝ)
    (hp : ∀ i,IsPenaltyFunction (p i)) :
    Convex ℝ {z : (Fin m → ℝ) × ℝ | z.2+(∑ i,p i (z.1 i))≤0} := by
  intro z hz w hw a b ha hb hab
  have hsum : (∑ i,p i (a*z.1 i+b*w.1 i)) ≤
      a*(∑ i,p i (z.1 i))+b*(∑ i,p i (w.1 i)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact (hp i).1.2 (mem_univ _) (mem_univ _) ha hb hab
  change a*z.2+b*w.2+(∑ i,p i (a*z.1 i+b*w.1 i))≤0
  have h1 := mul_le_mul_of_nonneg_left hz ha
  have h2 := mul_le_mul_of_nonneg_left hw hb
  nlinarith

lemma vp_necessary {N m : ℕ}
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hF : ConvexOn ℝ univ F) (hf : ∀ i,ConvexOn ℝ univ (f i))
    (p : Fin m → ℝ → ℝ) (hp : ∀ i,IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i,Tendsto (fun t => p i t/t) (𝓝[>]0) (𝓝 (c i)))
    (xs : EuclideanSpace ℝ (Fin N)) (hmin : ∀ x,penalized F f p xs≤penalized F f p x)
    (hsol : xs∈solutionSet F f) :
    ∃ U : Fin m → ℝ,IsLagrangeMultiplierVector F f U ∧ ∀ i,U i≤c i := by
  classical
  let C := vf_upper F f (F xs)
  let D : Set ((Fin m → ℝ) × ℝ) := {z | z.2+(∑ i,p i (z.1 i))≤0}
  have hdisj : Disjoint C D := by
    apply disjoint_left.mpr
    rintro z ⟨x,hg,hFx⟩ hz
    have hm := hmin x
    rw [vp_zero_on_feasible F f p hp hsol.1] at hm
    change F xs≤F x+(∑ i,p i (f i x)) at hm
    have hs : (∑ i,p i (f i x))≤∑ i,p i (z.1 i) :=
      Finset.sum_le_sum (fun i _ => vp_monotone (p i) (hp i) (hg i).le)
    change F x-F xs<z.2 at hFx
    change z.2+(∑ i,p i (z.1 i))≤0 at hz
    linarith
  obtain ⟨L,b,hC,hD⟩ := geometric_hahn_banach_open
    (vf_upper_convex F f (F xs) hF hf) (vf_upper_open F f (F xs))
    (vp_penalty_hypograph_convex p hp) hdisj
  have h0 : (0 : (Fin m → ℝ) × ℝ)∈D := by
    change (0:ℝ)+(∑ i,p i 0)≤0
    simp only [(fun i => (hp i).2.1 0 le_rfl),Finset.sum_const_zero,add_zero,le_refl]
  have hb0 : b≤0 := by simpa using hD 0 h0
  have hb1 : 0≤b := by
    have hct : Continuous (fun t : ℝ => L (fun _ : Fin m => t,t)) := by fun_prop
    have hlim : Tendsto (fun t : ℝ => L (fun _ : Fin m => t,t)) (𝓝[>]0) (𝓝 0) := by
      have hz : L (fun _ : Fin m => (0:ℝ),(0:ℝ))=0 := by
        change L 0=0
        exact map_zero L
      simpa only [hz] using (hct.tendsto 0).mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
    apply (hC (fun _ => t,t) ?_).le
    refine ⟨xs,fun i => (hsol.1 i).trans_lt ht,?_⟩
    simpa using ht
  have hb : b=0 := le_antisymm hb0 hb1
  let M := -L
  have hM : ∀ z∈vf_upper F f (F xs),0<M z := by
    intro z hz
    have h := hC z hz
    rw [hb] at h
    change 0< -L z
    linarith
  have hMD : ∀ z∈D,M z≤0 := by
    intro z hz
    have h := hD z hz
    rw [hb] at h
    change -L z≤0
    linarith
  obtain ⟨hu,ha0⟩ := vf_coeff_nonneg F f (F xs) M hM
  let u : Fin m → ℝ := fun i => M (Pi.single i (1:ℝ),0)
  let a : ℝ := M (0,1)
  have hsingle : ∀ i (t : ℝ), (Pi.single i t,-p i t)∈D := by
    intro i t
    change -p i t+(∑ j,p j (Pi.single (M:=fun _ => ℝ) i t j))≤0
    have he : (∑ j,p j (Pi.single (M:=fun _ => ℝ) i t j))=p i t := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Pi.single_eq_of_ne hji,(hp j).2.1 0 le_rfl]
      · simp
    rw [he]
    linarith
  have hcoeff : ∀ i (t : ℝ),u i*t≤a*p i t := by
    intro i t
    have h := hMD _ (hsingle i t)
    have he : Pi.single i t=t • Pi.single (M:=fun _ => ℝ) i (1:ℝ) := by
      ext j
      by_cases hj : j=i <;> simp [hj]
    rw [he,vf_split] at h
    simp only [Pi.smul_apply,smul_eq_mul] at h
    have hsum : (∑ j,M (Pi.single j (1:ℝ),0)*(t*Pi.single (M:=fun _ => ℝ) i (1:ℝ) j))=u i*t := by
      rw [Finset.sum_eq_single i]
      · simp [u,mul_comm]
      · intro j hj hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    rw [hsum] at h
    change u i*t+a*(-p i t)≤0 at h
    nlinarith
  have ha : 0<a := by
    by_contra hn
    have haz : a=0 := le_antisymm (le_of_not_gt hn) ha0
    have huz : ∀ i,u i=0 := by
      intro i
      have h := hcoeff i 1
      rw [haz,zero_mul,mul_one] at h
      exact le_antisymm h (hu i)
    have hmem : (fun i => f i xs+1,(1:ℝ))∈vf_upper F f (F xs) :=
      ⟨xs,fun i => by linarith,by simp⟩
    have h := hM _ hmem
    rw [vf_split] at h
    change 0<(∑ i,u i*(f i xs+1))+a*1 at h
    simp only [huz,haz,zero_mul,Finset.sum_const_zero,zero_add,lt_self_iff_false] at h
  let U : Fin m → ℝ := fun i => u i/a
  have hU : ∀ i,0≤U i := fun i => div_nonneg (hu i) ha.le
  have hbound : ∀ x,F xs≤F x+(∑ i,U i*f i x) := by
    intro x
    have h := vf_upper_bound F f (F xs) M hM hu ha x
    have he : a*(∑ i,U i*f i x)=∑ i,u i*f i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [U]
      field_simp [ne_of_gt ha]
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  have hglb : IsGLB (F '' feasibleSet f) (F xs) := by
    apply IsLeast.isGLB
    exact ⟨⟨xs,hsol.1,rfl⟩,by rintro _ ⟨x,hx,rfl⟩; exact hsol.2 x hx⟩
  refine ⟨U,⟨hU,F xs,hglb,hbound⟩,?_⟩
  intro i
  apply ge_of_tendsto (hc i)
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
  apply (le_div_iff₀ ht).mpr
  change (u i/a)*t≤p i t
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ ha).mpr (by nlinarith [hcoeff i t])

end
end ShorNonsmooth.Decomposition

-- Shared checked proof: ValueFnPenaltyComplete

namespace ShorNonsmooth.Decomposition
open Set Filter Topology
noncomputable section

lemma vp_sufficient {N m : ℕ}
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (p : Fin m → ℝ → ℝ) (hp : ∀ i,IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i,Tendsto (fun t => p i t/t) (𝓝[>]0) (𝓝 (c i)))
    (xs : EuclideanSpace ℝ (Fin N)) (hmin : ∀ x,penalized F f p xs≤penalized F f p x)
    (U : Fin m → ℝ) (hU : IsLagrangeMultiplierVector F f U) (hUc : ∀ i,U i<c i) :
    solutionSet F f={x | ∀ x',penalized F f p x≤penalized F f p x'} := by
  obtain ⟨hU0,v,hglb,hdual⟩ := hU
  have hgap := vp_penalty_dual_gap f p hp c hc U hU0 hUc
  have hlower : ∀ x,v≤penalized F f p x := by
    intro x
    have h := (hgap x).1
    change v≤F x+(∑ i,p i (f i x))
    linarith [hdual x]
  have hstrict : ∀ x,x∉feasibleSet f → v<penalized F f p x := by
    intro x hx
    have h := (hgap x).2 hx
    change v<F x+(∑ i,p i (f i x))
    linarith [hdual x]
  have hxsle : penalized F f p xs≤v := by
    apply hglb.2
    rintro _ ⟨x,hx,rfl⟩
    simpa only [vp_zero_on_feasible F f p hp hx] using hmin x
  have hxseq : penalized F f p xs=v := le_antisymm hxsle (hlower xs)
  have hxsf : xs∈feasibleSet f := by
    by_contra hn
    have h := hstrict xs hn
    rw [hxseq] at h
    exact lt_irrefl v h
  have hxsF : F xs=v := by
    rw [vp_zero_on_feasible F f p hp hxsf] at hxseq
    exact hxseq
  ext x
  constructor
  · intro hx
    have hxF : F x=v := by
      have h1 := hx.2 xs hxsf
      have h2 := hglb.1 ⟨x,hx.1,rfl⟩
      rw [hxsF] at h1
      exact le_antisymm h1 h2
    intro y
    rw [vp_zero_on_feasible F f p hp hx.1,hxF]
    exact hlower y
  · intro hx
    have hxle : penalized F f p x≤v := by simpa only [hxseq] using hx xs
    have hxf : x∈feasibleSet f := by
      by_contra hn
      have h := hstrict x hn
      linarith
    refine ⟨hxf,?_⟩
    intro y hy
    rw [vp_zero_on_feasible F f p hp hxf] at hxle
    exact hxle.trans (hglb.1 ⟨y,hy,rfl⟩)

lemma vp_exact {N m : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf : ∀ i,ConvexOn ℝ univ (f i))
    (p : Fin m → ℝ → ℝ) (hp : ∀ i,IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i,Tendsto (fun t => p i t/t) (𝓝[>]0) (𝓝 (c i)))
    (xstar : EuclideanSpace ℝ (Fin N)) (hxstar : ∀ x,penalized f₀ f p xstar≤penalized f₀ f p x) :
    (xstar∈solutionSet f₀ f → ∃ U : Fin m → ℝ,IsLagrangeMultiplierVector f₀ f U ∧ ∀ i,U i≤c i) ∧
    ∀ U : Fin m → ℝ,IsLagrangeMultiplierVector f₀ f U → (∀ i,U i<c i) →
    solutionSet f₀ f={x | ∀ x',penalized f₀ f p x≤penalized f₀ f p x'} := by
  exact ⟨vp_necessary f₀ f hf₀ hf p hp c hc xstar hxstar,
    fun U hU hUc => vp_sufficient f₀ f p hp c hc xstar hxstar U hU hUc⟩

end
end ShorNonsmooth.Decomposition

open ShorNonsmooth.Decomposition
open MeasureTheory Filter Topology

open Filter Topology

/-- Shor (1985), **Theorem 4.2** (p. 147), for the convex program (4.178) `min f₀(x)` s.t. `f_i(x) ≤ 0` and
the penalized function (4.179) `S(x) = f₀(x) + Σ p_i[f_i(x)]` with nonsmooth penalty functions `p_i`
(convex, `0` on `t ≤ 0`, positive on `t > 0`), `c_i = lim_{t→0+} p_i(t)/t`, and a point `x*` minimizing
`S` over all `x` (standing assumption, p. 146):

1. (necessity) if `x*` is a solution of (4.178), then `c_i ≥ ȳ_i` for all `i` for some Lagrange
   multiplier vector `ȳ` of (4.178);
2. if `ȳ` is a Lagrange multiplier vector of (4.178) with `c_i > ȳ_i` for all `i`, then the sets of
   minimum points of (4.178) and of `S` are equal.

The book's "a Lagrange multiplier vector" is read existentially in (1) (the universal reading is false
when the multiplier is not unique). -/
theorem solution {N m : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀) (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (p : Fin m → ℝ → ℝ) (hp : ∀ i, IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i, Tendsto (fun t => p i t / t) (𝓝[>] 0) (𝓝 (c i)))
    (xstar : EuclideanSpace ℝ (Fin N)) (hxstar : ∀ x, penalized f₀ f p xstar ≤ penalized f₀ f p x) :
    (xstar ∈ solutionSet f₀ f →
        ∃ ybar : Fin m → ℝ, IsLagrangeMultiplierVector f₀ f ybar ∧ ∀ i, ybar i ≤ c i) ∧
      ∀ ybar : Fin m → ℝ, IsLagrangeMultiplierVector f₀ f ybar → (∀ i, ybar i < c i) →
        solutionSet f₀ f = {x | ∀ x', penalized f₀ f p x ≤ penalized f₀ f p x'} := by
  exact vp_exact f₀ f hf₀ hf p hp c hc xstar hxstar

#print axioms solution
