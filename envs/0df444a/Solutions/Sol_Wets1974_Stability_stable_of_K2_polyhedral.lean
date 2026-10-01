-- Prove2me | solution 1 for Wets1974.Stability.stable_of_K2_polyhedral
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:17:19.959725+00:00
-- url     : https://prove2.me/submissions/2df98aca-0076-4288-b55d-300463b65580

import Mathlib.Analysis.LocallyConvex.Separation
import Definitions.Def_Wets1974_Stability_Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.EReal.Operations
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

private theorem lp_uniform_penalty {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ (q : Fin n → ℝ) (t : Fin m → ℝ),t∈posW W →
      ∀ y : Fin n → ℝ,(∀ j,0≤y j) →
        KallMayer.Recourse.LPValue W q t≤
          ((dotProduct q y+B*(∑ j,|q j|)*(∑ i,|t i-(W *ᵥ y) i|):ℝ):EReal) := by
  obtain ⟨B,hB,hbound⟩ := hoffman_fiber (1 : Matrix (Fin n) (Fin n) ℝ) W
  refine ⟨B,hB,?_⟩
  intro q t ht y hy
  have hne : ∃ z : Fin n → ℝ,(∀ i,(0:ℝ)≤((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) i) ∧ W *ᵥ z=t := by
    simpa only [Matrix.one_mulVec,posW,Set.mem_setOf_eq] using ht
  obtain ⟨z,hz,hWz,hn⟩ := hbound 0 t hne y (by simpa using hy)
  simp only [Matrix.one_mulVec,Pi.zero_apply] at hz
  have hcost : dotProduct q z≤dotProduct q y+B*(∑ j,|q j|)*(∑ i,|t i-(W *ᵥ y) i|) := by
    have hh : dotProduct q (z-y)≤(∑ j,|q j|)*‖z-y‖ := by
      calc
        _ ≤ ∑ j,|q j| *|z j-y j| := Finset.sum_le_sum (fun j _ => by simpa only [abs_mul,Pi.sub_apply] using le_abs_self (q j*(z j-y j)))
        _ ≤ ∑ j,|q j| *‖z-y‖ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm (z-y) j) (abs_nonneg _))
        _ = _ := by rw [Finset.sum_mul]
    have hh' := mul_le_mul_of_nonneg_left hn (show 0≤∑ j,|q j| from Finset.sum_nonneg (fun j _ => abs_nonneg (q j)))
    rw [dotProduct_sub] at hh
    nlinarith only [hh,hh']
  unfold KallMayer.Recourse.LPValue
  apply le_trans (sInf_le ?_) (EReal.coe_le_coe_iff.mpr hcost)
  exact ⟨z,hz,hWz,rfl⟩

private theorem lp_perturbation {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (B : ℝ) (hbound : ∀ (q : Fin n → ℝ) (t : Fin m → ℝ),t∈posW W →
      ∀ y : Fin n → ℝ,(∀ j,0≤y j) →
        KallMayer.Recourse.LPValue W q t≤
          ((dotProduct q y+B*(∑ j,|q j|)*(∑ i,|t i-(W *ᵥ y) i|):ℝ):EReal))
    (q : Fin n → ℝ) (t s : Fin m → ℝ) (ht : t∈posW W) :
    KallMayer.Recourse.LPValue W q t≤KallMayer.Recourse.LPValue W q s+
      ((B*(∑ j,|q j|)*(∑ i,|t i-s i|):ℝ):EReal) := by
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp
  apply le_sInf
  rintro r ⟨y,hy,hWy,rfl⟩
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
  have hh := hbound q t ht y hy
  simpa only [hWy,EReal.coe_add] using hh

private theorem lp_joint_measurable {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fun p : (Fin n → ℝ)×(Fin m → ℝ) => KallMayer.Recourse.LPValue W p.1 p.2) := by
  classical
  obtain ⟨B,hB,hbound⟩ := lp_uniform_penalty W
  let Y := {y : Fin n → ℝ // ∀ j,0≤y j}
  let F : ((Fin n → ℝ)×(Fin m → ℝ)) → EReal := fun p =>
    ⨅ y : Y, ((dotProduct p.1 y.val+B*(∑ j,|p.1 j|)*(∑ i,|p.2 i-(W *ᵥ y.val) i|):ℝ):EReal)
  have hFm : Measurable F := by
    apply UpperSemicontinuous.measurable
    apply upperSemicontinuous_iInf
    intro y
    apply Continuous.upperSemicontinuous
    apply continuous_coe_real_ereal.comp
    unfold dotProduct
    fun_prop
  have he (q : Fin n → ℝ) (t : Fin m → ℝ) (ht : t∈posW W) :
      KallMayer.Recourse.LPValue W q t=F (q,t) := by
    apply le_antisymm
    · apply le_iInf
      intro y
      exact hbound q t ht y.val y.property
    · apply le_sInf
      rintro r ⟨y,hy,hWy,rfl⟩
      have hh := iInf_le (fun y : Y => ((dotProduct q y.val+B*(∑ j,|q j|)*(∑ i,|t i-(W *ᵥ y.val) i|):ℝ):EReal)) (⟨y,hy⟩ : Y)
      simpa only [hWy,sub_self,abs_zero,Finset.sum_const_zero,mul_zero,add_zero] using hh
  have hne (q : Fin n → ℝ) (t : Fin m → ℝ) (ht : t∉posW W) : KallMayer.Recourse.LPValue W q t=⊤ := by
    unfold KallMayer.Recourse.LPValue
    have hempty : {r : EReal | ∃ y : Fin n → ℝ,(∀ j,0≤y j) ∧ W *ᵥ y=t ∧ r=(dotProduct q y:ℝ)}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro r ⟨y,hy,hWy,hr⟩
      exact ht ⟨y,hy,hWy⟩
    rw [hempty,sInf_empty]
  have hh : (fun p : (Fin n → ℝ)×(Fin m → ℝ) => KallMayer.Recourse.LPValue W p.1 p.2)=
      fun p => if p.2∈posW W then F p else ⊤ := by
    funext p
    split_ifs with hp
    · exact he p.1 p.2 hp
    · exact hne p.1 p.2 hp
  rw [hh]
  exact Measurable.ite ((posW_closed W).preimage continuous_snd).measurableSet hFm measurable_const

private theorem weighted_mat_norm {m n k : ℕ} (q : Fin n → ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (z : Fin k → ℝ) :
    (∑ j,|q j|)*(∑ i,|(T *ᵥ z) i|)≤(∑ j,∑ i,∑ l,|q j*T i l|)*‖z‖ := by
  have hi (i : Fin m) : |(T *ᵥ z) i|≤∑ l,|T i l| *|z l| := by
    simpa only [Matrix.mulVec,dotProduct,abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun l => T i l*z l)
  calc
    _ = ∑ j,∑ i,|q j| *|(T *ᵥ z) i| := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]
    _ ≤ ∑ j,∑ i,|q j| *(∑ l,|T i l| *|z l|) := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (abs_nonneg _)))
    _ = ∑ j,∑ i,∑ l,|q j*T i l| *|z l| := by simp only [Finset.mul_sum,abs_mul,mul_assoc]
    _ ≤ ∑ j,∑ i,∑ l,|q j*T i l| *‖z‖ := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm z l) (abs_nonneg _))))
    _ = _ := by simp only [Finset.sum_mul]

private theorem feasible_cost_bound {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ (t : Fin m → ℝ) (q : Fin n → ℝ),t∈posW W →
      KallMayer.Recourse.LPValue W q t≤((B*∑ j,∑ i,|q j*t i| : ℝ):EReal) := by
  obtain ⟨B,hB,hbound⟩ := lp_uniform_penalty W
  refine ⟨B,hB,?_⟩
  intro t q ht
  have hh := hbound q t ht 0 (by simp)
  have he : B*(∑ j,|q j|)*(∑ i,|t i|)=B*∑ j,∑ i,|q j*t i| := by
    rw [mul_assoc,Finset.sum_mul]
    simp only [Finset.mul_sum,abs_mul]
  simpa only [Matrix.mulVec_zero,Pi.zero_apply,sub_zero,dotProduct_zero,zero_add,he] using hh

private theorem Q_measurable {n nb mb : ℕ} (W : Matrix (Fin mb) (Fin nb) ℝ) (x : Fin n → ℝ) :
    Measurable (Q W x) := by
  change Measurable ((fun p : (Fin nb → ℝ)×(Fin mb → ℝ) => KallMayer.Recourse.LPValue W p.1 p.2) ∘ (fun ξ : DataSpace n nb mb => (qOf ξ,pOf ξ-TOf ξ *ᵥ x)))
  apply (lp_joint_measurable W).comp
  apply Continuous.measurable
  unfold qOf pOf TOf Matrix.mulVec dotProduct
  fun_prop

private theorem recourse_uniform_bound {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hcov : WeakCovariance μ) :
    ∃ H : DataSpace n nb mb → ℝ,Integrable H μ ∧ (∀ ξ,0≤H ξ) ∧
      ∀ x∈K2mu μ W,∀ y∈K2mu μ W,∀ᵐ ξ∂μ,
        Q W x ξ≤Q W y ξ+((H ξ*‖x-y‖:ℝ):EReal) := by
  obtain ⟨B,hB,hbound⟩ := lp_uniform_penalty W
  let H : DataSpace n nb mb → ℝ := fun ξ => B*∑ j,∑ i,∑ k,|qOf ξ j*TOf ξ i k|
  have hH : Integrable H μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j hj
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    exact (hcov.2.2 j i k).abs
  have hH0 (ξ) : 0≤H ξ := by dsimp [H]; positivity
  refine ⟨H,hH,hH0,?_⟩
  intro x hx y hy
  filter_upwards [hx,hy] with ξ hξx hξy
  have hh := lp_perturbation W B hbound (qOf ξ)
    (pOf ξ-TOf ξ *ᵥ x) (pOf ξ-TOf ξ *ᵥ y) hξx
  have he (i : Fin mb) :
      |(pOf ξ-TOf ξ *ᵥ x) i-(pOf ξ-TOf ξ *ᵥ y) i|=|(TOf ξ *ᵥ (x-y)) i| := by
    simp only [Pi.sub_apply,Matrix.mulVec_sub]
    rw [show (pOf ξ i-(TOf ξ *ᵥ x) i)-(pOf ξ i-(TOf ξ *ᵥ y) i)= -((TOf ξ *ᵥ x) i-(TOf ξ *ᵥ y) i) by ring,abs_neg]
  have hnorm := mul_le_mul_of_nonneg_left (weighted_mat_norm (qOf ξ) (TOf ξ) (x-y)) hB.le
  have hcost : B*(∑ j,|qOf ξ j|)*(∑ i,|(pOf ξ-TOf ξ *ᵥ x) i-(pOf ξ-TOf ξ *ᵥ y) i|)≤H ξ*‖x-y‖ := by
    simp only [he]
    simpa only [H,mul_assoc] using hnorm
  exact hh.trans (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr hcost))


private theorem residual_cont {n nb mb : ℕ} (x : Fin n → ℝ) :
    Continuous (fun ξ : DataSpace n nb mb => pOf ξ-TOf ξ *ᵥ x) := by
  unfold pOf TOf Matrix.mulVec dotProduct
  fun_prop

private theorem mu_eq_support {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) : K2mu μ W=K2supp μ W := by
  ext x
  have hc := (posW_closed W).preimage (residual_cont (nb := nb) x)
  constructor
  · intro hx
    exact μ.support_subset_of_isClosed hc hx
  · intro hx
    exact (show ∀ᵐ ξ ∂μ,ξ∈μ.support from μ.support_mem_ae).mono (fun ξ hξ => hx ξ hξ)

private theorem K2_eq_mu {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) : K2 μ W=K2mu μ W := by
  ext x
  have hc : IsClosed {ζ : PTSpace n mb | x∈K2of W ζ} :=
    (posW_closed W).preimage (residualMap x).continuous_of_finiteDimensional
  have ha : (∀ᵐ ζ ∂μ.map projPT,x∈K2of W ζ) ↔ x∈K2mu μ W :=
    ae_map_iff measurable_projPT.aemeasurable hc.measurableSet
  rw [← ha]
  constructor
  · intro hx
    have hx : ∀ ζ ∈ suppPT μ,x∈K2of W ζ := by simpa only [K2,Set.mem_iInter] using hx
    exact (show ∀ᵐ ζ ∂μ.map projPT,ζ∈(μ.map projPT).support from (μ.map projPT).support_mem_ae).mono (fun ζ hζ => hx ζ hζ)
  · intro hx
    have hh := (μ.map projPT).support_subset_of_isClosed hc hx
    simpa only [K2,suppPT,Set.mem_iInter,Set.subset_def,Set.mem_setOf_eq] using hh

private theorem expected_lt_top_iff {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (x : Fin n → ℝ) :
    expectedRecourse μ W x<⊤ ↔ (∫⁻ ξ,(Q W x ξ).toENNReal ∂μ)<⊤ := by
  unfold expectedRecourse paperIntegral
  split_ifs with hi
  · simp [hi]
  · constructor
    · intro _
      exact lt_top_iff_ne_top.mpr hi
    · intro _
      apply lt_top_iff_ne_top.mpr
      apply EReal.add_ne_top
      · exact EReal.coe_ennreal_eq_top_iff.not.mpr hi
      · intro hneg
        have hh := congrArg Neg.neg hneg
        simp only [neg_neg,EReal.neg_top] at hh
        exact EReal.coe_ennreal_ne_bot _ hh

private theorem infeasible_value {n nb mb : ℕ} (W : Matrix (Fin mb) (Fin nb) ℝ)
    (x : Fin n → ℝ) (ξ : DataSpace n nb mb) (hξ : pOf ξ-TOf ξ *ᵥ x∉posW W) : Q W x ξ=⊤ := by
  unfold Q KallMayer.Recourse.PointwiseRecourse KallMayer.Recourse.LPValue
  have he : {r : EReal | ∃ y : Fin nb → ℝ,(∀ j,0≤y j) ∧ W *ᵥ y=pOf ξ-TOf ξ *ᵥ x ∧ r=↑(dotProduct (qOf ξ) y)}=∅ := by
    ext r
    constructor
    · rintro ⟨y,hy,he,_⟩
      exact False.elim (hξ ⟨y,hy,he⟩)
    · simp
  rw [he]
  exact sInf_empty

private theorem strong_subset_mu {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) : K2s μ W⊆K2mu μ W := by
  intro x hx
  have hfinite := (expected_lt_top_iff μ W x).mp hx
  let F := {ξ : DataSpace n nb mb | pOf ξ-TOf ξ *ᵥ x∉posW W}
  have hF : MeasurableSet F := ((posW_closed W).preimage (residual_cont (nb := nb) x)).isOpen_compl.measurableSet
  have hcmp : (∫⁻ ξ,F.indicator (fun _ => (⊤:ENNReal)) ξ ∂μ)≤∫⁻ ξ,(Q W x ξ).toENNReal ∂μ := by
    apply lintegral_mono
    intro ξ
    by_cases hξ : ξ∈F
    · rw [Set.indicator_of_mem hξ]
      change ⊤≤(Q W x ξ).toENNReal
      rw [infeasible_value W x ξ hξ,EReal.toENNReal_top]
    · simp only [Set.indicator_of_notMem hξ,zero_le]
  rw [lintegral_indicator_const hF] at hcmp
  have hzero : μ F=0 := by
    by_contra hn
    rw [ENNReal.top_mul hn] at hcmp
    exact (not_le_of_gt hfinite) hcmp
  change ∀ᵐ ξ ∂μ,pOf ξ-TOf ξ *ᵥ x∈posW W
  exact hzero

private theorem mu_subset_strong {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hcov : WeakCovariance μ) : K2mu μ W⊆K2s μ W := by
  obtain ⟨B,hB,hbound⟩ := feasible_cost_bound W
  intro x hx
  let R := fun ξ : DataSpace n nb mb => pOf ξ-TOf ξ *ᵥ x
  let G := fun ξ : DataSpace n nb mb => B*∑ j,∑ i,|qOf ξ j*R ξ i|
  have hG : Integrable G μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j hj
    apply integrable_finsetSum
    intro i hi
    apply Integrable.abs
    have hp := hcov.2.1 j i
    have ht : Integrable (fun ξ => ∑ k,qOf ξ j*TOf ξ i k*x k) μ := by
      apply integrable_finsetSum
      intro k hk
      exact (hcov.2.2 j i k).mul_const (x k)
    convert! hp.sub ht using 1
    funext ξ
    simp [R,Matrix.mulVec,dotProduct,mul_sub,Finset.mul_sum,mul_assoc]
  have hcmp : (∫⁻ ξ,(Q W x ξ).toENNReal ∂μ)≤∫⁻ ξ,ENNReal.ofReal (G ξ) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hx] with ξ hξ
    have hh := hbound (R ξ) (qOf ξ) hξ
    have hh := EReal.toENNReal_le_toENNReal hh
    simpa only [Q,KallMayer.Recourse.PointwiseRecourse,G,R,EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),EReal.toReal_coe] using hh
  exact (expected_lt_top_iff μ W x).mpr (hcmp.trans_lt hG.lintegral_lt_top)
private theorem paper_congr {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {g h : X → EReal} (he : g=ᵐ[μ]h) : paperIntegral μ g=paperIntegral μ h := by
  have hp : (∫⁻ x,(g x).toENNReal ∂μ)=∫⁻ x,(h x).toENNReal ∂μ := lintegral_congr_ae (he.mono (fun _ hh => congrArg _ hh))
  have hn : (∫⁻ x,(-g x).toENNReal ∂μ)=∫⁻ x,(-h x).toENNReal ∂μ := lintegral_congr_ae (he.mono (fun _ hh => congrArg (fun r : EReal => (-r).toENNReal) hh))
  simp only [paperIntegral,hp,hn]

private theorem paper_coe {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℝ) (hg : Integrable g μ) : paperIntegral μ (fun x => (g x:EReal))=((∫ x,g x ∂μ):ℝ) := by
  have hp := hg.lintegral_lt_top
  have hn : (∫⁻ x,ENNReal.ofReal (-g x) ∂μ)<⊤ := hg.neg.lintegral_lt_top
  unfold paperIntegral
  rw [if_neg (show (∫⁻ x,((g x:ℝ):EReal).toENNReal ∂μ)≠⊤ from hp.ne)]
  simp only [EReal.real_coe_toENNReal,← EReal.coe_neg]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg,EReal.coe_sub,
    EReal.coe_ennreal_toReal hp.ne,EReal.coe_ennreal_toReal hn.ne]

private theorem paper_finite {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → EReal) (hg : Measurable g)
    (hp : (∫⁻ x,(g x).toENNReal ∂μ)<⊤) (hb : paperIntegral μ g≠⊥) :
    (∀ᵐ x∂μ,g x≠⊤ ∧ g x≠⊥) ∧ Integrable (fun x => (g x).toReal) μ ∧
      paperIntegral μ g=((∫ x,(g x).toReal ∂μ):ℝ) := by
  have hn : (∫⁻ x,(-g x).toENNReal ∂μ)<⊤ := by
    by_contra hn
    have hn : (∫⁻ x,(-g x).toENNReal ∂μ)=⊤ := eq_top_iff.mpr (le_of_not_gt hn)
    apply hb
    simp [paperIntegral,hp.ne,hn,EReal.sub_top]
  have hat := ae_lt_top hg.ereal_toENNReal hp.ne
  have hab := ae_lt_top hg.neg.ereal_toENNReal hn.ne
  have hae : ∀ᵐ x∂μ,g x≠⊤ ∧ g x≠⊥ := by
    filter_upwards [hat,hab] with x hxt hxb
    constructor
    · intro hh; simpa [hh] using hxt
    · intro hh; simpa [hh] using hxb
  have hpos := integrable_toReal_of_lintegral_ne_top hg.ereal_toENNReal.aemeasurable hp.ne
  have hneg := integrable_toReal_of_lintegral_ne_top hg.neg.ereal_toENNReal.aemeasurable hn.ne
  have hreal : Integrable (fun x => (g x).toReal) μ := by
    convert hpos.sub hneg using 1
    funext x
    change (g x).toReal=(g x).toENNReal.toReal-(-g x).toENNReal.toReal
    induction g x with
    | bot => simp
    | top => simp
    | coe r =>
      simp only [EReal.toReal_coe,EReal.real_coe_toENNReal,← EReal.coe_neg]
      rcases le_total 0 r with hr|hr
      · rw [ENNReal.toReal_ofReal hr,ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hr)]
        simp
      · rw [ENNReal.ofReal_of_nonpos hr,ENNReal.toReal_ofReal (neg_nonneg.mpr hr)]
        simp
  refine ⟨hae,hreal,?_⟩
  have he : g=ᵐ[μ](fun x => ((g x).toReal:EReal)) := hae.mono (fun x hx => (EReal.coe_toReal hx.1 hx.2).symm)
  rw [paper_congr μ he,paper_coe μ _ hreal]

private theorem ereal_transfer {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g h : X → EReal) (G : X → ℝ) (hh : Measurable h)
    (hg : Integrable (fun x => (g x).toReal) μ) (hG : Integrable G μ)
    (hgf : ∀ᵐ x∂μ,g x≠⊤ ∧ g x≠⊥)
    (hb : ∀ᵐ x∂μ,h x≤g x+(G x:ℝ) ∧ g x≤h x+(G x:ℝ)) :
    (∀ᵐ x∂μ,h x≠⊤ ∧ h x≠⊥) ∧ Integrable (fun x => (h x).toReal) μ ∧
      (∀ᵐ x∂μ,|(h x).toReal-(g x).toReal|≤G x) := by
  have hfin : ∀ᵐ x∂μ,h x≠⊤ ∧ h x≠⊥ := by
    filter_upwards [hgf,hb] with x hg hb
    have he := EReal.coe_toReal hg.1 hg.2
    constructor
    · intro ht
      have hp := hb.1
      rw [ht,← he,← EReal.coe_add] at hp
      exact EReal.coe_ne_top _ (top_le_iff.mp hp)
    · intro ht
      have hp := hb.2
      rw [ht,EReal.bot_add] at hp
      exact hg.2 (le_bot_iff.mp hp)
  have hnorm : ∀ᵐ x∂μ,|(h x).toReal-(g x).toReal|≤G x := by
    filter_upwards [hgf,hfin,hb] with x hg hf hb
    have eg := EReal.coe_toReal hg.1 hg.2
    have eh := EReal.coe_toReal hf.1 hf.2
    rw [← eg,← eh,← EReal.coe_add,← EReal.coe_add] at hb
    have h1 := EReal.coe_le_coe_iff.mp hb.1
    have h2 := EReal.coe_le_coe_iff.mp hb.2
    exact abs_sub_le_iff.mpr ⟨by linarith only [h1],by linarith only [h2]⟩
  refine ⟨hfin,?_,hnorm⟩
  apply (hg.norm.add hG).mono' hh.ereal_toReal.aestronglyMeasurable
  filter_upwards [hnorm] with x hx
  have hh := abs_add_le ((h x).toReal-(g x).toReal) ((g x).toReal)
  rw [sub_add_cancel] at hh
  change |(h x).toReal|≤|(g x).toReal|+G x
  linarith only [hh,hx]

private theorem expected_regular {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hcov : WeakCovariance μ)
    (x0 : Fin n → ℝ) (hx0 : x0∈K2 μ W) (hb0 : expectedRecourse μ W x0≠⊥) :
    ∃ C : ℝ,0≤C ∧
      (∀ x∈K2 μ W,(∀ᵐ ξ∂μ,Q W x ξ≠⊤ ∧ Q W x ξ≠⊥) ∧
        Integrable (fun ξ => (Q W x ξ).toReal) μ ∧
        expectedRecourse μ W x=((∫ ξ,(Q W x ξ).toReal ∂μ):ℝ)) ∧
      ∀ x∈K2 μ W,∀ y∈K2 μ W,
        |(expectedRecourse μ W x).toReal-(expectedRecourse μ W y).toReal|≤C*‖x-y‖ := by
  obtain ⟨H,hH,hH0,hbound⟩ := recourse_uniform_bound μ W hcov
  have hx0m : x0∈K2mu μ W := by rwa [← K2_eq_mu]
  have hp0 : (∫⁻ ξ,(Q W x0 ξ).toENNReal ∂μ)<⊤ :=
    (expected_lt_top_iff μ W x0).mp (mu_subset_strong μ W hcov hx0m)
  obtain ⟨hf0,hi0,hv0⟩ := paper_finite μ (Q W x0) (Q_measurable W x0) hp0 hb0
  have hreg (x : Fin n → ℝ) (hx : x∈K2 μ W) :
      (∀ᵐ ξ∂μ,Q W x ξ≠⊤ ∧ Q W x ξ≠⊥) ∧
        Integrable (fun ξ => (Q W x ξ).toReal) μ ∧
        expectedRecourse μ W x=((∫ ξ,(Q W x ξ).toReal ∂μ):ℝ) := by
    have hxm : x∈K2mu μ W := by rwa [← K2_eq_mu]
    have hh : ∀ᵐ ξ∂μ,Q W x ξ≤Q W x0 ξ+((H ξ*‖x-x0‖:ℝ):EReal) ∧
        Q W x0 ξ≤Q W x ξ+((H ξ*‖x-x0‖:ℝ):EReal) := by
      filter_upwards [hbound x hxm x0 hx0m,hbound x0 hx0m x hxm] with ξ h1 h2
      exact ⟨h1,by simpa only [norm_sub_rev x0 x] using h2⟩
    obtain ⟨hf,hi,habs⟩ := ereal_transfer μ (Q W x0) (Q W x) (fun ξ => H ξ*‖x-x0‖)
      (Q_measurable W x) hi0 (hH.mul_const _) hf0 hh
    refine ⟨hf,hi,?_⟩
    unfold expectedRecourse
    rw [paper_congr μ (hf.mono (fun ξ hξ => (EReal.coe_toReal hξ.1 hξ.2).symm)),paper_coe μ _ hi]
  refine ⟨∫ ξ,H ξ ∂μ,integral_nonneg hH0,hreg,?_⟩
  intro x hx y hy
  obtain ⟨hfx,hix,hvx⟩ := hreg x hx
  obtain ⟨hfy,hiy,hvy⟩ := hreg y hy
  have hxm : x∈K2mu μ W := by rwa [← K2_eq_mu]
  have hym : y∈K2mu μ W := by rwa [← K2_eq_mu]
  have hh : ∀ᵐ ξ∂μ,Q W x ξ≤Q W y ξ+((H ξ*‖x-y‖:ℝ):EReal) ∧
      Q W y ξ≤Q W x ξ+((H ξ*‖x-y‖:ℝ):EReal) := by
    filter_upwards [hbound x hxm y hym,hbound y hym x hxm] with ξ h1 h2
    exact ⟨h1,by simpa only [norm_sub_rev y x] using h2⟩
  obtain ⟨hf,hi,habs⟩ := ereal_transfer μ (Q W y) (Q W x) (fun ξ => H ξ*‖x-y‖)
    (Q_measurable W x) hiy (hH.mul_const _) hfy hh
  have hle := integral_mono_ae (hix.sub hiy).norm (hH.mul_const ‖x-y‖) habs
  have hnorm := norm_integral_le_integral_norm (μ := μ) (fun ξ => (Q W x ξ).toReal-(Q W y ξ).toReal)
  rw [integral_sub hix hiy] at hnorm
  rw [integral_mul_const] at hle
  rw [hvx,hvy,EReal.toReal_coe,EReal.toReal_coe]
  exact hnorm.trans hle

private theorem lp_convex_value {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (t s : Fin m → ℝ) (a b r0 r1 : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hab : a+b=1)
    (h0 : KallMayer.Recourse.LPValue W q t=(r0:ℝ))
    (h1 : KallMayer.Recourse.LPValue W q s=(r1:ℝ)) :
    KallMayer.Recourse.LPValue W q (a • t+b • s)≤((a*r0+b*r1:ℝ):EReal) := by
  by_contra hn
  obtain ⟨c,hcl,hcr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hcl : a*r0+b*r1<c := EReal.coe_lt_coe_iff.mp hcl
  let e := (c-(a*r0+b*r1))/2
  have he : 0<e := by dsimp [e]; linarith only [hcl]
  have hyt : KallMayer.Recourse.LPValue W q t<((r0+e:ℝ):EReal) := by rw [h0];exact EReal.coe_lt_coe_iff.mpr (by linarith only [he])
  have hys : KallMayer.Recourse.LPValue W q s<((r1+e:ℝ):EReal) := by rw [h1];exact EReal.coe_lt_coe_iff.mpr (by linarith only [he])
  obtain ⟨v,⟨y,hy,hWy,rfl⟩,hcy⟩ := sInf_lt_iff.mp hyt
  obtain ⟨v,⟨z,hz,hWz,rfl⟩,hcz⟩ := sInf_lt_iff.mp hys
  have hcy := EReal.coe_lt_coe_iff.mp hcy
  have hcz := EReal.coe_lt_coe_iff.mp hcz
  have hcost : dotProduct q (a • y+b • z)<c := by
    have hcy' := mul_le_mul_of_nonneg_left hcy.le ha
    have hcz' := mul_le_mul_of_nonneg_left hcz.le hb
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
    change a*dotProduct q y+b*dotProduct q z<c
    have heq : a*(r0+e)+b*(r1+e)=a*r0+b*r1+e := by nlinarith only [congrArg (fun u : ℝ => u*e) hab]
    dsimp [e] at heq hcy' hcz'
    nlinarith only [hcy',hcz',heq,hcl]
  have hle : KallMayer.Recourse.LPValue W q (a • t+b • s)≤((dotProduct q (a • y+b • z):ℝ):EReal) := by
    apply sInf_le
    refine ⟨a • y+b • z,fun j => add_nonneg (mul_nonneg ha (hy j)) (mul_nonneg hb (hz j)),?_,rfl⟩
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hWy,hWz]
  exact (not_lt_of_ge hle) (hcr.trans' (EReal.coe_lt_coe_iff.mpr hcost))

private theorem residual_affine {n nb mb : ℕ} (ξ : DataSpace n nb mb)
    (x y : Fin n → ℝ) (a b : ℝ) (hab : a+b=1) :
    pOf ξ-TOf ξ *ᵥ (a • x+b • y)=a • (pOf ξ-TOf ξ *ᵥ x)+b • (pOf ξ-TOf ξ *ᵥ y) := by
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith only [congrArg (fun r : ℝ => r*pOf ξ i) hab]

private theorem K2_convex {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) : Convex ℝ (K2 μ W) := by
  rw [K2_eq_mu]
  intro x hx y hy a b ha hb hab
  change ∀ᵐ ξ∂μ,pOf ξ-TOf ξ *ᵥ (a • x+b • y)∈posW W
  filter_upwards [hx,hy] with ξ hξx hξy
  obtain ⟨u,hu,hWu⟩ := hξx
  obtain ⟨v,hv,hWv⟩ := hξy
  refine ⟨a • u+b • v,fun j => add_nonneg (mul_nonneg ha (hu j)) (mul_nonneg hb (hv j)),?_⟩
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hWu,hWv,residual_affine ξ x y a b hab]

private theorem expected_convex {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hreg : ∀ x∈K2 μ W,(∀ᵐ ξ∂μ,Q W x ξ≠⊤ ∧ Q W x ξ≠⊥) ∧
      Integrable (fun ξ => (Q W x ξ).toReal) μ ∧ expectedRecourse μ W x=((∫ ξ,(Q W x ξ).toReal ∂μ):ℝ)) :
    ConvexOn ℝ (K2 μ W) (fun x => (expectedRecourse μ W x).toReal) := by
  refine ⟨K2_convex μ W,?_⟩
  intro x hx y hy a b ha hb hab
  have hm := K2_convex μ W hx hy ha hb hab
  obtain ⟨hfx,hix,hvx⟩ := hreg x hx
  obtain ⟨hfy,hiy,hvy⟩ := hreg y hy
  obtain ⟨hfm,him,hvm⟩ := hreg (a • x+b • y) hm
  have hpoint : ∀ᵐ ξ∂μ,(Q W (a • x+b • y) ξ).toReal≤a*(Q W x ξ).toReal+b*(Q W y ξ).toReal := by
    filter_upwards [hfx,hfy,hfm] with ξ hξx hξy hξm
    have hh := lp_convex_value W (qOf ξ) (pOf ξ-TOf ξ *ᵥ x) (pOf ξ-TOf ξ *ᵥ y) a b
      (Q W x ξ).toReal (Q W y ξ).toReal ha hb hab
      (EReal.coe_toReal hξx.1 hξx.2).symm (EReal.coe_toReal hξy.1 hξy.2).symm
    rw [← residual_affine ξ x y a b hab] at hh
    change Q W (a • x+b • y) ξ≤_ at hh
    rw [← EReal.coe_toReal hξm.1 hξm.2] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hh := integral_mono_ae him ((hix.const_mul a).add (hiy.const_mul b)) hpoint
  dsimp only [Pi.add_apply] at hh
  rw [integral_add (hix.const_mul a) (hiy.const_mul b),integral_const_mul,integral_const_mul] at hh
  simpa only [hvm,hvx,hvy,EReal.toReal_coe,smul_eq_mul] using hh

private theorem dot_lipschitz {n : ℕ} (c x y : Fin n → ℝ) :
    |dotProduct c x-dotProduct c y|≤(∑ j,|c j|)*‖x-y‖ := by
  rw [← dotProduct_sub]
  calc
    _ ≤ ∑ j,|c j| *|x j-y j| := by simpa only [dotProduct,Pi.sub_apply,abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => c j*(x-y) j)
    _ ≤ ∑ j,|c j| *‖x-y‖ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm (x-y) j) (abs_nonneg _))
    _ = _ := by rw [Finset.sum_mul]


open Wets1974.Stability

private theorem Z_regular {n nb mb : ℕ} (μ : Measure (Wets1974.Stability.DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hcov : Wets1974.Stability.WeakCovariance μ)
    (x0 : Fin n → ℝ) (hx0 : x0∈Wets1974.Stability.K2 μ W) (hb0 : Z μ W x0≠⊥) :
    (∀ x∈Wets1974.Stability.K2 μ W,Z μ W x≠⊤ ∧ Z μ W x≠⊥) ∧
      ConvexOn ℝ (Wets1974.Stability.K2 μ W) (fun x => (Z μ W x).toReal) ∧
      ∃ L : NNReal,LipschitzOnWith L (fun x => (Z μ W x).toReal) (Wets1974.Stability.K2 μ W) := by
  have hb : Wets1974.Feasibility.expectedRecourse μ W x0≠⊥ := by
    intro hh
    apply hb0
    change ((cbar μ ⬝ᵥ x0:ℝ):EReal)+Wets1974.Feasibility.expectedRecourse μ W x0=⊥
    rw [hh,EReal.add_bot]
  obtain ⟨C,hC,hreg,hbound⟩ := expected_regular μ W hcov x0 hx0 hb
  have hE := expected_convex μ W hreg
  have hK : Convex ℝ (Wets1974.Stability.K2 μ W) := K2_convex μ W
  have he (x : Fin n → ℝ) (hx : x∈Wets1974.Stability.K2 μ W) :
      Z μ W x=((dotProduct (cbar μ) x+(Wets1974.Feasibility.expectedRecourse μ W x).toReal:ℝ):EReal) := by
    change ((dotProduct (cbar μ) x:ℝ):EReal)+Wets1974.Feasibility.expectedRecourse μ W x=_
    rw [(hreg x hx).2.2,EReal.toReal_coe,← EReal.coe_add]
  have hr (x : Fin n → ℝ) (hx : x∈Wets1974.Stability.K2 μ W) :
      (Z μ W x).toReal=dotProduct (cbar μ) x+(Wets1974.Feasibility.expectedRecourse μ W x).toReal := by
    rw [he x hx,EReal.toReal_coe]
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [he x hx]
    exact ⟨EReal.coe_ne_top _,EReal.coe_ne_bot _⟩
  · refine ⟨hK,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hE.2 hx hy ha hb hab
    dsimp only at hh ⊢
    rw [hr _ (hK hx hy ha hb hab),hr x hx,hr y hy]
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul] at hh ⊢
    nlinarith only [hh]
  · let D := (∑ j,|cbar μ j|)+C
    have hD : 0≤D := add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hC
    refine ⟨⟨D,hD⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    rw [Real.dist_eq,dist_eq_norm,hr x hx,hr y hy]
    have hh := hbound x hx y hy
    have hd := dot_lipschitz (cbar μ) x y
    have htri := abs_add_le (dotProduct (cbar μ) x-dotProduct (cbar μ) y)
      ((Wets1974.Feasibility.expectedRecourse μ W x).toReal-(Wets1974.Feasibility.expectedRecourse μ W y).toReal)
    have heq : dotProduct (cbar μ) x+(Wets1974.Feasibility.expectedRecourse μ W x).toReal-
        (dotProduct (cbar μ) y+(Wets1974.Feasibility.expectedRecourse μ W y).toReal)=
        (dotProduct (cbar μ) x-dotProduct (cbar μ) y)+
        ((Wets1974.Feasibility.expectedRecourse μ W x).toReal-(Wets1974.Feasibility.expectedRecourse μ W y).toReal) := by ring
    rw [heq]
    change |_|≤D*‖x-y‖
    dsimp [D]
    nlinarith only [hh,hd,htri]

private theorem K1_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (K1 A b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨?_,fun j => add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg hc (hy.2 j))⟩
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hx.1,hy.1,← add_smul,hac,one_smul]

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

private theorem stable_poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
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

theorem solution {n nb mb m : ℕ} (μ : Measure (Wets1974.Stability.DataSpace n nb mb))
    [IsProbabilityMeasure μ] (hcov : Wets1974.Stability.WeakCovariance μ)
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hW : FullRowRank W)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hK2 : Wets1974.Stability.IsPolyhedron (Wets1974.Stability.K2 μ W))
    (hfin : IsFiniteProgram (Z μ W) (Wets1974.Stability.K2 μ W) A b) :
    IsStable (Z μ W) (Wets1974.Stability.K2 μ W) A b := by
  obtain ⟨v,hv⟩ := hfin
  have hne : (K1 A b∩Wets1974.Stability.K2 μ W).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hh := hv
    unfold progValue at hh
    rw [he,Set.image_empty,sInf_empty] at hh
    exact EReal.coe_ne_top v hh.symm
  obtain ⟨x,hx⟩ := hne
  have hxb : Z μ W x≠⊥ := by
    intro hb
    have hh : (v:ℝ)≤Z μ W x := by rw [← hv];exact sInf_le ⟨x,hx,rfl⟩
    rw [hb] at hh
    exact EReal.coe_ne_bot v (le_bot_iff.mp hh)
  obtain ⟨hfinite,hconv,hlip⟩ := Z_regular μ W hcov x hx.2 hxb
  have he (y : Fin n → ℝ) (hy : y∈Wets1974.Stability.K2 μ W) :
      (((Z μ W y).toReal:ℝ):EReal)=Z μ W y := EReal.coe_toReal (hfinite y hy).1 (hfinite y hy).2
  have hprog : progValue (fun y => (((Z μ W y).toReal:ℝ):EReal)) (Wets1974.Stability.K2 μ W) A b=
      progValue (Z μ W) (Wets1974.Stability.K2 μ W) A b := by
    unfold progValue
    apply congrArg sInf
    apply Set.image_congr
    intro y hy
    exact he y hy.2
  have hfin' : IsFiniteProgram (fun y => (((Z μ W y).toReal:ℝ):EReal)) (Wets1974.Stability.K2 μ W) A b :=
    ⟨v,hprog.trans hv⟩
  obtain ⟨v',hv',π,hπ⟩ := stable_poly A b (Wets1974.Stability.K2 μ W) hK2
    (fun y => (Z μ W y).toReal) hconv hlip hfin'
  refine ⟨v',hprog.symm.trans hv',π,?_⟩
  intro y hy hy0
  have hh := hπ y hy hy0
  dsimp only at hh
  rwa [he y hy] at hh
