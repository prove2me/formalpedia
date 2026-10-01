-- Prove2me | solution 1 for Wets1974.Stability.stable_of_lipschitz_on_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:56:32.959982+00:00
-- url     : https://prove2.me/submissions/b14c546b-3f7c-4de8-a716-15d2dd6f1c33

import Definitions.Def_Wets1974_Stability_ConvexAnalysis
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Definitions.Def_Wets1974_Feasibility_Model
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic
open Set Filter Topology

private theorem cone_reduce {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S,0 < a i) :
    ∃ T : Finset ι,T ⊆ S ∧ LinearIndependent ℝ (fun i : T => c i) ∧
      ∃ q : ι → ℝ,(∀ i ∈ T,0 ≤ q i) ∧
        ∑ i ∈ T,q i • c i = ∑ i ∈ S,a i • c i := by
  classical
  induction S using Finset.strongInductionOn generalizing a with
  | _ S ih =>
    by_cases hli : LinearIndependent ℝ (fun i : S => c i)
    · exact ⟨S,Finset.Subset.refl _,hli,a,fun i hi => (ha i hi).le,rfl⟩
    have hdep : ¬ LinearIndepOn ℝ c (S : Set ι) := hli
    rw [linearIndepOn_finset_iff] at hdep
    push_neg at hdep
    obtain ⟨b,hb,j,hj,hbj⟩:=hdep
    have hbpos : ∃ b : ι → ℝ,(∑ i ∈ S,b i • c i)=0 ∧ ∃ j ∈ S,0 < b j := by
      rcases lt_or_gt_of_ne hbj with hneg | hpos
      · refine ⟨fun i => -b i,?_,j,hj,by linarith⟩
        simp only [neg_smul,Finset.sum_neg_distrib,hb,neg_zero]
      · exact ⟨b,hb,j,hj,hpos⟩
    obtain ⟨b,hb,j,hj,hbj⟩:=hbpos
    let P := S.filter (fun i => 0 < b i)
    have hP : P.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨hj,hbj⟩⟩
    obtain ⟨j,hjP,hmin⟩:=Finset.exists_min_image P (fun i => a i/b i) hP
    have hj:= (Finset.mem_filter.mp hjP).1
    have hbj:=(Finset.mem_filter.mp hjP).2
    let t := a j/b j
    have ht : 0 < t := div_pos (ha j hj) hbj
    let d : ι → ℝ := fun i => a i-t*b i
    have hd : ∀ i ∈ S,0 ≤ d i := by
      intro i hi
      by_cases hbipos : 0 < b i
      · have hh:=hmin i (Finset.mem_filter.mpr ⟨hi,hbipos⟩)
        have hh' : t*b i ≤ a i := (le_div_iff₀ hbipos).mp hh
        dsimp [d]; linarith
      · have hh : t*b i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hbipos)
        dsimp [d]; linarith [ha i hi]
    have hdj : d j=0 := by dsimp [d,t]; field_simp; ring
    let U := S.filter (fun i => 0 < d i)
    have hUS : U ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,?_⟩
      intro he
      have hh : j ∈ U := he.symm ▸ hj
      have := (Finset.mem_filter.mp hh).2
      rw [hdj] at this
      exact lt_irrefl _ this
    obtain ⟨T,hTU,hTI,q,hq,he⟩:=ih U hUS d (fun i hi => (Finset.mem_filter.mp hi).2)
    refine ⟨T,hTU.trans (Finset.filter_subset _ _),hTI,q,hq,?_⟩
    rw [he]
    calc
      ∑ i ∈ U,d i • c i = ∑ i ∈ S,d i • c i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hni
        have hle : d i ≤ 0 := by
          by_contra! hh
          exact hni (Finset.mem_filter.mpr ⟨hi,hh⟩)
        rw [le_antisymm hle (hd i hi),zero_smul]
      _ = ∑ i ∈ S,a i • c i-t • (∑ i ∈ S,b i • c i) := by
        simp only [d,sub_smul,mul_smul,Finset.sum_sub_distrib,Finset.smul_sum]
      _ = ∑ i ∈ S,a i • c i := by rw [hb,smul_zero,sub_zero]


private theorem finite_cone_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) :
    IsClosed {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i} := by
  classical
  let D (T : Finset ι) : Set E :=
    if LinearIndependent ℝ (fun i : T => c i) then
      (Fintype.linearCombination ℝ (fun i : T => c i)) '' {a : T → ℝ | ∀ i,0 ≤ a i}
    else ∅
  have hD : ∀ T,IsClosed (D T) := by
    intro T
    dsimp [D]
    split_ifs with hli
    · have hi := LinearMap.isClosedEmbedding_of_injective
        (LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp hli))
      apply hi.isClosedMap _
      simp only [setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_empty
  have he : {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i} = ⋃ T,D T := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      let S := Finset.univ.filter (fun i => 0<a i)
      obtain ⟨T,hTS,hli,q,hq,heq⟩:=cone_reduce c S a (fun i hi => (Finset.mem_filter.mp hi).2)
      have heq' : ∑ i ∈ T,q i • c i = ∑ i,a i • c i := by
        rw [heq]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hh : a i=0 := by
          apply le_antisymm _ (ha i)
          by_contra! hh
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
        rw [hh,zero_smul]
      apply Set.mem_iUnion.mpr
      refine ⟨T,?_⟩
      dsimp [D]
      rw [if_pos hli]
      refine ⟨fun i => q i,fun i => hq i i.property,?_⟩
      change (∑ i : T,q i • c i)=_
      exact (Finset.sum_coe_sort T (fun i => q i • c i)).trans heq'
    · intro hy
      obtain ⟨T,hT⟩:=Set.mem_iUnion.mp hy
      dsimp [D] at hT
      split_ifs at hT with hli
      · obtain ⟨a,ha,rfl⟩:=hT
        refine ⟨fun i => if hi : i∈T then a ⟨i,hi⟩ else 0,?_,?_⟩
        · intro i; dsimp; split_ifs <;> simp_all
        · simp only [Fintype.linearCombination_apply]
          let q : ι → ℝ := fun i => if hi : i∈T then a ⟨i,hi⟩ else 0
          change (∑ i : T,a i • c i)=∑ i,q i • c i
          calc
            (∑ i : T,a i • c i) = ∑ i : T,q i • c i := by simp [q]
            _ = ∑ i ∈ T,q i • c i := Finset.sum_coe_sort T (fun i => q i • c i)
            _ = ∑ i,q i • c i := Finset.sum_subset (Finset.subset_univ _) (by
              intro i _ hi
              simp [q,hi])
      · exact False.elim hT
  rw [he]
  exact isClosed_iUnion_of_finite hD



open Matrix MeasureTheory Wets1974.Feasibility

private theorem posW_closed {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : IsClosed (posW W) := by
  have he : posW W={v : Fin m → ℝ | ∃ a : Fin n → ℝ,(∀ j,0 ≤ a j) ∧ v=∑ j,a j • (fun i => W i j)} := by
    ext v
    constructor
    · rintro ⟨a,ha,hav⟩
      refine ⟨a,ha,?_⟩
      rw [← hav]
      ext i
      simp [Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]
    · rintro ⟨a,ha,hav⟩
      refine ⟨a,ha,?_⟩
      rw [hav]
      ext i
      simp [Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]
  rw [he]
  exact finite_cone_closed _

private def posW_cone {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin m → ℝ) where
  carrier := posW W
  zero_mem' := ⟨0,by simp,by simp⟩
  add_mem' := by
    rintro a b ⟨y,hy,rfl⟩ ⟨z,hz,rfl⟩
    exact ⟨y+z,fun j => add_nonneg (hy j) (hz j),Matrix.mulVec_add _ _ _⟩
  smul_mem' := by
    rintro a b ⟨y,hy,rfl⟩
    exact ⟨(a:ℝ) • y,fun j => mul_nonneg a.property (hy j),Matrix.mulVec_smul _ _ _⟩

private def residualMap {n m : ℕ} (x : Fin n → ℝ) : PTSpace n m →ₗ[ℝ] (Fin m → ℝ) where
  toFun ζ := ζ.1-Matrix.of ζ.2 *ᵥ x
  map_add' := by
    intro ζ η
    ext i
    simp [Matrix.mulVec,dotProduct,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c ζ
    ext i
    simp [Matrix.mulVec,dotProduct,mul_assoc,← Finset.mul_sum]
    ring

private theorem hull_test {n nb mb : ℕ} (W : Matrix (Fin mb) (Fin nb) ℝ)
    (S : Set (PTSpace n mb)) (x : Fin n → ℝ) :
    (∀ ζ ∈ closedPosHull S, x ∈ K2of W ζ) ↔ ∀ ζ ∈ S,x ∈ K2of W ζ := by
  let C := (posW_cone W).comap (residualMap x)
  have hC : IsClosed (C : Set (PTSpace n mb)) :=
    (posW_closed W).preimage (residualMap x).continuous_of_finiteDimensional
  change (closedPosHull S ⊆ (C : Set (PTSpace n mb))) ↔ S ⊆ C
  constructor
  · intro h ζ hζ
    apply h
    exact subset_closure (PointedCone.subset_hull hζ)
  · intro h
    apply hC.closure_subset_iff.mpr
    exact Submodule.span_le.mpr h


private theorem cone_coeff_bound_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) :
    ∃ B : ℝ,0<B ∧ ∀ a : ι → ℝ,(∀ i,0≤a i) →
      ∃ b : ι → ℝ,(∀ i,0≤b i) ∧ (∑ i,b i • c i)=(∑ i,a i • c i) ∧
        (∀ i,|b i|≤B*‖∑ i,a i • c i‖) ∧ (∀ i,a i=0 → b i=0) := by
  classical
  have hK : ∀ T : Finset ι,∃ K : ℝ,0≤K ∧
      ∀ hli : LinearIndependent ℝ (fun i : T => c i),∀ q : T → ℝ,
        ‖q‖≤K*‖∑ i : T,q i • c i‖ := by
    intro T
    by_cases hli : LinearIndependent ℝ (fun i : T => c i)
    · let f := Fintype.linearCombination ℝ (fun i : T => c i)
      obtain ⟨K,hK,hanti⟩ := f.injective_iff_antilipschitz.mp
        (linearIndependent_iff_injective_fintypeLinearCombination.mp hli)
      refine ⟨K,K.coe_nonneg,?_⟩
      intro _ q
      exact ZeroHomClass.bound_of_antilipschitz f hanti q
    · exact ⟨0,le_rfl,fun hh => False.elim (hli hh)⟩
  choose K hK0 hK using hK
  let B := (∑ T : Finset ι,K T)+1
  have hB : 0<B := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset ι))) => hK0 T)
    dsimp [B]
    linarith
  have hKB (T : Finset ι) : K T≤B := by
    have hh := Finset.single_le_sum (fun T (_ : T∈(Finset.univ : Finset (Finset ι))) => hK0 T) (Finset.mem_univ T)
    dsimp [B]
    linarith
  refine ⟨B,hB,?_⟩
  intro a ha
  let S := Finset.univ.filter (fun i => 0<a i)
  obtain ⟨T,hTS,hli,q,hq,heq⟩ := cone_reduce c S a (fun i hi => (Finset.mem_filter.mp hi).2)
  have heq' : ∑ i ∈ T,q i • c i=∑ i,a i • c i := by
    rw [heq]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hh : a i=0 := by
      apply le_antisymm _ (ha i)
      by_contra! hh
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    rw [hh,zero_smul]
  let b := fun i => if hi : i∈T then q i else 0
  have hbeq : (∑ i,b i • c i)=∑ i∈T,q i • c i := by
    simp only [b,dite_eq_ite,ite_smul,zero_smul]
    simp [Finset.sum_ite_mem]
  refine ⟨b,?_,hbeq.trans heq',?_,?_⟩
  · intro i
    dsimp [b]
    split_ifs with hi
    · exact hq i hi
    · exact le_rfl
  · intro i
    by_cases hi : i∈T
    · have hh := hK T hli (fun i : T => q i)
      rw [Finset.sum_coe_sort T (fun i => q i • c i),heq'] at hh
      have hh0 := norm_le_pi_norm (fun i : T => q i) (⟨i,hi⟩ : T)
      dsimp [b]
      rw [if_pos hi]
      exact hh0.trans (hh.trans (mul_le_mul_of_nonneg_right (hKB T) (norm_nonneg _)))
    · dsimp [b]
      rw [if_neg hi,abs_zero]
      positivity


  · intro i hai
    have hi : i∉T := by
      intro hi
      have hh := (Finset.mem_filter.mp (hTS hi)).2
      rw [hai] at hh
      exact lt_irrefl _ hh
    simp [b,hi]

private theorem finite_farkas {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (c : ι → E) (g : E)
    (hg : ∀ v : E,(∀ i,0 ≤ inner ℝ (c i) v) → 0 ≤ inner ℝ g v) :
    ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ g=∑ i,a i • c i := by
  classical
  let C : ProperCone ℝ E := {
    carrier := {y : E | ∃ a : ι → ℝ,(∀ i,0 ≤ a i) ∧ y=∑ i,a i • c i}
    zero_mem' := ⟨0,by simp,by simp⟩
    add_mem' := by
      rintro x y ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
      refine ⟨a+b,fun i => add_nonneg (ha i) (hb i),?_⟩
      simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    smul_mem' := by
      rintro r x ⟨a,ha,rfl⟩
      refine ⟨fun i => (r:ℝ)*a i,fun i => mul_nonneg r.property (ha i),?_⟩
      change (r:ℝ) • (∑ i,a i • c i)=_
      simp only [Finset.smul_sum,mul_smul]
    isClosed' := finite_cone_closed c }
  change g∈C
  by_contra hn
  obtain ⟨v,hv,hgv⟩:=C.hyperplane_separation' hn
  have hci : ∀ i,0 ≤ inner ℝ (c i) v := by
    intro i
    apply hv _
    refine ⟨fun j => if j=i then 1 else 0,?_,?_⟩
    · intro j; dsimp; split_ifs <;> norm_num
    · simp
  exact (not_lt_of_ge (hg v hci)) hgv

private theorem poly_nearest_normal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {n : ℕ} (c : Fin n → E) (δ : Fin n → ℝ)
    (p x : E) (hp : ∀ i,δ i≤ inner ℝ (c i) p)
    (hn : ∀ y,(∀ i,δ i≤ inner ℝ (c i) y) → inner ℝ (x-p) (y-p)≤0) :
    ∃ a : Fin n → ℝ,(∀ i,0≤a i) ∧ p-x=∑ i,a i • c i ∧
      ∀ i,inner ℝ (c i) p≠δ i → a i=0 := by
  classical
  let S := Finset.univ.filter (fun i => inner ℝ (c i) p=δ i)
  have hd : ∀ v : E,(∀ i : S,0≤ inner ℝ (c i) v) → 0≤ inner ℝ (p-x) v := by
    intro v hv
    have hf : ∀ᶠ t in 𝓝[>] (0:ℝ),∀ i,δ i≤ inner ℝ (c i) (p+t • v) := by
      rw [eventually_all]
      intro i
      by_cases hi : inner ℝ (c i) p=δ i
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have hh := hv ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
        simp only [inner_add_right,real_inner_smul_right,hi]
        exact le_add_of_nonneg_right (mul_nonneg (show 0≤t from le_of_lt ht) hh)
      · have hstrict : δ i< inner ℝ (c i) p := lt_of_le_of_ne (hp i) (Ne.symm hi)
        have hc : Continuous (fun t : ℝ => inner ℝ (c i) (p+t • v)) := by fun_prop
        have hh : ∀ᶠ t in 𝓝 (0:ℝ),δ i < inner ℝ (c i) (p+t • v) :=
          hc.continuousAt.eventually (eventually_gt_nhds (by simpa using hstrict))
        exact (hh.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
    have ht : ∀ᶠ t in 𝓝[>] (0:ℝ),0<t := self_mem_nhdsWithin
    obtain ⟨t,ht,hf⟩ := (ht.and hf).exists
    have hh := hn _ hf
    simp only [add_sub_cancel_left,real_inner_smul_right,inner_sub_left] at hh ⊢
    nlinarith only [ht,hh]
  obtain ⟨a,ha,he⟩ := finite_farkas (fun i : S => c i) (p-x) hd
  let b := fun i => if hi : i∈S then a ⟨i,hi⟩ else 0
  refine ⟨b,?_,?_,?_⟩
  · intro i
    dsimp [b]
    split_ifs with hi
    · exact ha _
    · exact le_rfl
  · rw [he]
    calc
      (∑ i : S,a i • c i) = ∑ i : S,b i • c i := by simp [b]
      _ = ∑ i∈S,b i • c i := Finset.sum_coe_sort S (fun i => b i • c i)
      _ = ∑ i,b i • c i := Finset.sum_subset (Finset.subset_univ _) (by intro i _ hi; simp [b,hi])
  · intro i hi
    have hn : i∉S := by simpa [S] using hi
    simp [b,hn]

private theorem hoffman_halfspaces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {n : ℕ} (c : Fin n → E) :
    ∃ B : ℝ,0<B ∧ ∀ (δ : Fin n → ℝ), (∃ y : E,∀ i,δ i≤ inner ℝ (c i) y) →
      ∀ x : E,∃ p : E,(∀ i,δ i≤ inner ℝ (c i) p) ∧
        ‖p-x‖≤B*∑ i,max (δ i-inner ℝ (c i) x) 0 := by
  obtain ⟨B,hB,hbound⟩ := cone_coeff_bound_support c
  refine ⟨B,hB,?_⟩
  intro δ hne x
  let Ω := {y : E | ∀ i,δ i≤ inner ℝ (c i) y}
  have hc : IsClosed Ω := by
    simp only [Ω,Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_const.inner continuous_id)
  have hv : Convex ℝ Ω := by
    intro y hy z hz a b ha hb hab i
    simp only [inner_add_right,real_inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hy i) ha
    have h2 := mul_le_mul_of_nonneg_left (hz i) hb
    have he : (a+b)*δ i=δ i := by rw [hab,one_mul]
    nlinarith only [h1,h2,he]
  obtain ⟨p,hp,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv x
  have hn := (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp hmin
  obtain ⟨a,ha,he,hs⟩ := poly_nearest_normal c δ p x hp (fun y hy => hn y hy)
  obtain ⟨b,hb,hbe,hbn,hbs⟩ := hbound a ha
  rw [← he] at hbe hbn
  have hact (i : Fin n) : b i*(inner ℝ (c i) p-inner ℝ (c i) x)≤b i*max (δ i-inner ℝ (c i) x) 0 := by
    by_cases hi : inner ℝ (c i) p=δ i
    · rw [hi]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hb i)
    · rw [hbs i (hs i hi)]
      simp
  have hnorm : ‖p-x‖^2≤B*‖p-x‖*(∑ i,max (δ i-inner ℝ (c i) x) 0) := by
    calc
      ‖p-x‖^2 = inner ℝ (p-x) (p-x) := (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i,b i*inner ℝ (c i) (p-x) := by rw [← hbe,sum_inner]; simp only [real_inner_smul_left]
      _ ≤ ∑ i,b i*max (δ i-inner ℝ (c i) x) 0 := by simp only [inner_sub_right];exact Finset.sum_le_sum (fun i _ => hact i)
      _ ≤ ∑ i,(B*‖p-x‖)*max (δ i-inner ℝ (c i) x) 0 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right ((le_abs_self (b i)).trans (hbn i)) (le_max_right _ _))
      _ = _ := by rw [Finset.mul_sum]
  refine ⟨p,hp,?_⟩
  by_cases he : ‖p-x‖=0
  · rw [he]
    exact mul_nonneg hB.le (Finset.sum_nonneg (fun i _ => le_max_right _ _))
  · have hp : 0<‖p-x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    nlinarith only [hnorm,hp]

private theorem hoffman_matrix {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ δ : Fin m → ℝ,(∃ y : Fin n → ℝ,∀ i,δ i≤(G *ᵥ y) i) →
      ∀ x : Fin n → ℝ,∃ p : Fin n → ℝ,(∀ i,δ i≤(G *ᵥ p) i) ∧
        ‖p-x‖≤B*∑ i,max (δ i-(G *ᵥ x) i) 0 := by
  let c : Fin m → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (G i)
  have hi (i : Fin m) (y : EuclideanSpace ℝ (Fin n)) : inner ℝ (c i) y=(G *ᵥ WithLp.ofLp y) i := by
    simp [c,EuclideanSpace.inner_eq_star_dotProduct,Matrix.mulVec,dotProduct,mul_comm]
  obtain ⟨B,hB,hbound⟩ := hoffman_halfspaces c
  refine ⟨B,hB,?_⟩
  intro δ hne x
  have hne' : ∃ y : EuclideanSpace ℝ (Fin n),∀ i,δ i≤ inner ℝ (c i) y := by
    obtain ⟨y,hy⟩ := hne
    exact ⟨WithLp.toLp 2 y,by simpa only [hi,WithLp.ofLp_toLp] using hy⟩
  obtain ⟨p,hp,hn⟩ := hbound δ hne' (WithLp.toLp 2 x)
  refine ⟨WithLp.ofLp p,by simpa only [hi] using hp,?_⟩
  simp only [hi,WithLp.ofLp_toLp] at hn
  apply le_trans _ hn
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (p-WithLp.toLp 2 x) i

private theorem hoffman_fiber {k m n : ℕ} (G : Matrix (Fin k) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ (δ : Fin k → ℝ) (b : Fin m → ℝ),
      (∃ y : Fin n → ℝ,(∀ i,δ i≤(G *ᵥ y) i) ∧ A *ᵥ y=b) →
      ∀ x : Fin n → ℝ,(∀ i,δ i≤(G *ᵥ x) i) →
        ∃ p : Fin n → ℝ,(∀ i,δ i≤(G *ᵥ p) i) ∧ A *ᵥ p=b ∧
          ‖p-x‖≤B*∑ i,|b i-(A *ᵥ x) i| := by
  classical
  let I := (Fin k ⊕ Fin m) ⊕ Fin m
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let H : Matrix (Fin (Fintype.card I)) (Fin n) ℝ := fun i j =>
    Sum.elim (Sum.elim (fun l => G l j) (fun l => A l j)) (fun l => -A l j) (e.symm i)
  let d : (Fin k → ℝ) → (Fin m → ℝ) → Fin (Fintype.card I) → ℝ := fun δ b i =>
    Sum.elim (Sum.elim δ b) (fun j => -b j) (e.symm i)
  have hH (δ : Fin k → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
      (∀ i,d δ b i≤(H *ᵥ y) i) ↔ (∀ i,δ i≤(G *ᵥ y) i) ∧ A *ᵥ y=b := by
    constructor
    · intro h
      refine ⟨fun i => by simpa [d,H,Matrix.mulVec,dotProduct] using h (e (Sum.inl (Sum.inl i))),?_⟩
      ext j
      have hp := h (e (Sum.inl (Sum.inr j)))
      have hm := h (e (Sum.inr j))
      have hp' : b j≤(A *ᵥ y) j := by simpa [d,H,Matrix.mulVec,dotProduct] using hp
      have hm' : -(b j)≤-((A *ᵥ y) j) := by simpa [d,H,Matrix.mulVec,dotProduct,Finset.sum_neg_distrib] using hm
      linarith only [hp',hm']
    · rintro ⟨hG,hA⟩ i
      obtain ⟨i,rfl⟩ := e.surjective i
      rcases i with (i|i)|i
      · simpa [d,H,Matrix.mulVec,dotProduct] using hG i
      · simpa [d,H,Matrix.mulVec,dotProduct] using (le_of_eq (congrFun hA i).symm)
      · have hh : -b i≤-((A *ᵥ y) i) := by rw [hA]
        simpa [d,H,Matrix.mulVec,dotProduct,Finset.sum_neg_distrib] using hh
  obtain ⟨B,hB,hbound⟩ := hoffman_matrix H
  refine ⟨B,hB,?_⟩
  intro δ b hne x hx
  have hne' : ∃ y : Fin n → ℝ,∀ i,d δ b i≤(H *ᵥ y) i := by
    obtain ⟨y,hy,hAy⟩ := hne
    exact ⟨y,(hH δ b y).mpr ⟨hy,hAy⟩⟩
  obtain ⟨p,hp,hn⟩ := hbound (d δ b) hne' x
  obtain ⟨hp,hAp⟩ := (hH δ b p).mp hp
  refine ⟨p,hp,hAp,?_⟩
  have he : (∑ i,max (d δ b i-(H *ᵥ x) i) 0)=∑ i,|b i-(A *ᵥ x) i| := by
    rw [← e.sum_comp]
    change (∑ i : ((Fin k ⊕ Fin m) ⊕ Fin m),max (d δ b (e i)-(H *ᵥ x) (e i)) 0)=_
    simp only [Fintype.sum_sum_type,d,H,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Matrix.mulVec,dotProduct]
    have hzero (i : Fin k) : max (δ i-(∑ j,G i j*x j)) 0=0 := max_eq_right (sub_nonpos.mpr (hx i))
    simp only [hzero,Finset.sum_const_zero,zero_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [neg_mul,Finset.sum_neg_distrib]
    change max (b i-dotProduct (A i) x) 0+max (-b i- -dotProduct (A i) x) 0=|b i-dotProduct (A i) x|
    rcases le_total 0 (b i-dotProduct (A i) x) with hi|hi
    · rw [max_eq_left hi,max_eq_right (by linarith),add_zero,abs_of_nonneg hi]
    · rw [max_eq_right hi,max_eq_left (by linarith),zero_add,abs_of_nonpos hi]
      ring
  rwa [he] at hn
private theorem penalty_multiplier {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (S : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hc : ConvexOn ℝ S f) (v C : ℝ) (hC : 0≤C)
    (hne : ∃ x∈S,A *ᵥ x=b)
    (hpen : ∀ x∈S,v≤f x+C*∑ i,|(A *ᵥ x) i-b i|) :
    ∃ π : Fin m → ℝ,∀ x∈S,v≤f x+dotProduct π (b-A *ᵥ x) := by
  let U : Set ((Fin m → ℝ)×ℝ) := {p | p.2+C*∑ i,|p.1 i-b i|<v}
  let T : Set ((Fin m → ℝ)×ℝ) := {p | ∃ x∈S,A *ᵥ x=p.1 ∧ f x≤p.2}
  have hu : Convex ℝ U := by
    intro p hp q hq a d ha hd had
    change (a*p.2+d*q.2)+C*∑ i,|(a*p.1 i+d*q.1 i)-b i|<v
    have hsum : (∑ i,|(a*p.1 i+d*q.1 i)-b i|)≤a*(∑ i,|p.1 i-b i|)+d*(∑ i,|q.1 i-b i|) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have he : (a*p.1 i+d*q.1 i)-b i=a*(p.1 i-b i)+d*(q.1 i-b i) := by nlinarith [congrArg (fun t : ℝ => t*b i) had]
      rw [he]
      calc
        _ ≤ |a*(p.1 i-b i)|+|d*(q.1 i-b i)| := abs_add_le _ _
        _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hd]
    have hh := mul_le_mul_of_nonneg_left hsum hC
    have hp' := hp
    have hq' := hq
    change p.2+C*(∑ i,|p.1 i-b i|)<v at hp'
    change q.2+C*(∑ i,|q.1 i-b i|)<v at hq'
    have hstrict : a*(p.2+C*(∑ i,|p.1 i-b i|))+d*(q.2+C*(∑ i,|q.1 i-b i|))<v := by
      rcases eq_or_lt_of_le ha with he|he
      · have hd1 : d=1 := by linarith only [had,he]
        simpa [← he,hd1] using hq'
      · have hp'' := mul_lt_mul_of_pos_left hp' he
        have hq'' := mul_le_mul_of_nonneg_left hq'.le hd
        have hev : (a+d)*v=v := by rw [had,one_mul]
        nlinarith only [hp'',hq'',hev]
    nlinarith only [hh,hstrict]
  have huo : IsOpen U := by
    apply isOpen_lt _ continuous_const
    fun_prop
  have ht : Convex ℝ T := by
    intro p hp q hq a d ha hd had
    obtain ⟨x,hx,hAx,hfx⟩ := hp
    obtain ⟨y,hy,hAy,hfy⟩ := hq
    refine ⟨a • x+d • y,hc.1 hx hy ha hd had,?_,?_⟩
    · simp [Matrix.mulVec_add,Matrix.mulVec_smul,hAx,hAy]
    · have hh := hc.2 hx hy ha hd had
      have h1 := mul_le_mul_of_nonneg_left hfx ha
      have h2 := mul_le_mul_of_nonneg_left hfy hd
      change f (a • x+d • y)≤a*p.2+d*q.2
      change f (a • x+d • y)≤a*f x+d*f y at hh
      linarith only [hh,h1,h2]
  have hdis : Disjoint U T := by
    apply Set.disjoint_left.mpr
    intro p hp hpt
    obtain ⟨x,hx,hAx,hfx⟩ := hpt
    have hh := hpen x hx
    change p.2+C*(∑ i,|p.1 i-b i|)<v at hp
    rw [hAx] at hh
    linarith only [hh,hp,hfx]
  obtain ⟨F,u,hU,hT⟩ := geometric_hahn_banach_open hu huo ht hdis
  let L := F.toLinearMap.comp (LinearMap.inl ℝ (Fin m → ℝ) ℝ)
  let d := F (0,1)
  have he (z : Fin m → ℝ) (r : ℝ) : F (z,r)=L z+d*r := by
    have hp : (z,r)=(z,0)+r • ((0,1):(Fin m → ℝ)×ℝ) := by simp
    rw [hp,map_add,map_smul]
    simp [L,d,mul_comm]
  obtain ⟨x0,hx0,hAx0⟩ := hne
  have hfx0 : v≤f x0 := by simpa [hAx0] using hpen x0 hx0
  have hu0 := hU (b,v-1) (by dsimp [U]; simp)
  have ht0 := hT (b,f x0) ⟨x0,hx0,hAx0,le_rfl⟩
  rw [he] at hu0 ht0
  have hd : 0<d := by
    by_contra hn
    have hn : d≤0 := le_of_not_gt hn
    have hmul := mul_nonpos_of_nonpos_of_nonneg hn (show 0≤f x0-v+1 by linarith)
    nlinarith only [hu0,ht0,hmul]
  have hv : F (b,v)≤u := by
    apply le_of_forall_lt
    intro z hz
    let r := (z-L b)/d
    have hr : r<v := by
      apply (div_lt_iff₀ hd).mpr
      rw [he] at hz
      linarith only [hz]
    have hUr : (b,r)∈U := by simpa [U] using hr
    have hh := hU (b,r) hUr
    have hzr : F (b,r)=z := by rw [he]; dsimp [r]; field_simp [ne_of_gt hd] <;> ring
    rwa [hzr] at hh
  let π : Fin m → ℝ := fun i => -(L (Pi.single i 1))/d
  have hπ (z : Fin m → ℝ) : dotProduct π z= -(L z)/d := by
    have hz : z=∑ i,z i • Pi.single i (1:ℝ) := by ext i; simp [Pi.single_apply]
    conv_rhs => rw [hz,map_sum]
    simp only [map_smul,smul_eq_mul,dotProduct,π]
    rw [← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  refine ⟨π,?_⟩
  intro x hx
  have hh := hv.trans (hT (A *ᵥ x,f x) ⟨x,hx,rfl,le_rfl⟩)
  rw [he,he] at hh
  rw [hπ,map_sub]
  have hdne := ne_of_gt hd
  have heq : f x + -(L b-L (A *ᵥ x))/d=(f x*d-(L b-L (A *ᵥ x)))/d := by
    field_simp [hdne] <;> ring
  rw [heq]
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hh]

open Wets1974.Stability

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (P : Set (Fin n → ℝ)) (hP : Wets1974.Stability.IsPolyhedron P) (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ P f) (hlip : ∃ L : NNReal, LipschitzOnWith L f P)
    (hfin : IsFiniteProgram (fun x => (f x : EReal)) P A b) :
    IsStable (fun x => (f x : EReal)) P A b := by
  classical
  obtain ⟨v,hv⟩ := hfin
  have hfeas : (K1 A b∩P).Nonempty := by
    by_contra hn
    have he : K1 A b∩P=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hh := hv
    unfold progValue at hh
    rw [he,Set.image_empty,sInf_empty] at hh
    exact EReal.coe_ne_top v hh.symm
  have hvle (x : Fin n → ℝ) (hx : x∈K1 A b∩P) : v≤f x := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hv]
    exact sInf_le ⟨x,hx,rfl⟩
  obtain ⟨k,G,δ,hP⟩ := hP
  let I := Fin k ⊕ Fin n
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let H : Matrix (Fin (Fintype.card I)) (Fin n) ℝ := fun i j =>
    Sum.elim (fun l => G l j) (fun l => if l=j then 1 else 0) (e.symm i)
  let d : Fin (Fintype.card I) → ℝ := fun i => Sum.elim δ (fun _ => 0) (e.symm i)
  let S := {x : Fin n → ℝ | x∈P ∧ ∀ j,0≤x j}
  have hS (x : Fin n → ℝ) : (∀ i,d i≤(H *ᵥ x) i) ↔ x∈S := by
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · rw [hP]
        intro i
        simpa [d,H,Matrix.mulVec,dotProduct] using h (e (Sum.inl i))
      · intro j
        simpa [d,H,Matrix.mulVec,dotProduct] using h (e (Sum.inr j))
    · rintro ⟨hx,hx0⟩ i
      obtain ⟨i,rfl⟩ := e.surjective i
      rcases i with i|i
      · have hh : δ i≤(G *ᵥ x) i := by rw [hP] at hx; exact hx i
        simpa [d,H,Matrix.mulVec,dotProduct] using hh
      · simpa [d,H,Matrix.mulVec,dotProduct] using hx0 i
  have hne : ∃ x∈S,A *ᵥ x=b := by
    obtain ⟨x,hx⟩ := hfeas
    exact ⟨x,⟨hx.2,hx.1.2⟩,hx.1.1⟩
  have hne' : ∃ x : Fin n → ℝ,(∀ i,d i≤(H *ᵥ x) i) ∧ A *ᵥ x=b := by
    obtain ⟨x,hx,hAx⟩ := hne
    exact ⟨x,(hS x).mpr hx,hAx⟩
  have hcS : ConvexOn ℝ S f := by
    apply hconv.subset (fun x hx => hx.1)
    intro x hx y hy a c ha hc hac
    refine ⟨hconv.1 hx.1 hy.1 ha hc hac,?_⟩
    intro j
    exact add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg hc (hy.2 j))
  obtain ⟨B,hB,hbound⟩ := hoffman_fiber H A
  obtain ⟨L,hL⟩ := hlip
  have hpen : ∀ x∈S,v≤f x+(L:ℝ)*B*∑ i,|(A *ᵥ x) i-b i| := by
    intro x hx
    obtain ⟨y,hy,hAy,hn⟩ := hbound d b hne' x ((hS x).mpr hx)
    have hy := (hS y).mp hy
    have hh := hvle y ⟨⟨hAy,hy.2⟩,hy.1⟩
    have hl : |f y-f x|≤(L:ℝ)*‖y-x‖ := hL.norm_sub_le hy.1 hx.1
    have hn' := mul_le_mul_of_nonneg_left hn L.coe_nonneg
    simp only [abs_sub_comm (b _)] at hn'
    have hh' := le_abs_self (f y-f x)
    nlinarith only [hh,hl,hn',hh']
  obtain ⟨π,hπ⟩ := penalty_multiplier A b S f hcS v ((L:ℝ)*B)
    (mul_nonneg L.coe_nonneg hB.le) hne hpen
  refine ⟨v,hv,π,?_⟩
  intro x hx hx0
  simpa only [← EReal.coe_add,EReal.coe_le_coe_iff] using hπ x ⟨hx,hx0⟩
