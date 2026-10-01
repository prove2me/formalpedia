-- Prove2me | solution 1 for SteinitzExchange.Duality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:41:50.935585+00:00
-- url     : https://prove2.me/submissions/13c4f6af-443b-42af-bffc-e38851e185b2

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_SteinitzExchange_Duality_Problems
import Mathlib.Analysis.Convex.Combination
import Definitions.Def_Wets1974_Stability_ConvexAnalysis
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

private theorem eliminate_scalar {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) :
    (∃ t : ℝ,∀ i,b i≤a i+c i*t) ↔
      (∀ i,c i=0 → b i≤a i) ∧
      ∀ i j,0<c i → c j<0 → (b i-a i)/c i≤(b j-a j)/c j := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    constructor
    · intro i hi
      simpa only [hi,zero_mul,add_zero] using ht i
    · intro i j hi hj
      have hil : (b i-a i)/c i≤t := (div_le_iff₀ hi).mpr (by nlinarith only [ht i])
      have hjr : t≤(b j-a j)/c j := (le_div_iff_of_neg hj).mpr (by nlinarith only [ht j])
      exact hil.trans hjr
  · rintro ⟨hzero,hpair⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0<c i)
    let U : Finset ι := Finset.univ.filter (fun i => c i<0)
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image L (fun i => (b i-a i)/c i) hL
      have hci : 0<c i := (Finset.mem_filter.mp hi).2
      refine ⟨(b i-a i)/c i,?_⟩
      intro j
      rcases lt_trichotomy (c j) 0 with hj|hj|hj
      · have hh := (le_div_iff_of_neg hj).mp (hpair i j hci hj)
        nlinarith only [hh]
      · simpa only [hj,zero_mul,add_zero] using hzero j hj
      · have hh := (div_le_iff₀ hj).mp (hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))
        nlinarith only [hh]
    · by_cases hU : U.Nonempty
      · obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image U (fun i => (b i-a i)/c i) hU
        refine ⟨(b i-a i)/c i,?_⟩
        intro j
        rcases lt_trichotomy (c j) 0 with hj|hj|hj
        · have hh := (le_div_iff_of_neg hj).mp (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))
          nlinarith only [hh]
        · simpa only [hj,zero_mul,add_zero] using hzero j hj
        · exact False.elim (hL ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
      · refine ⟨0,?_⟩
        intro j
        have hj : c j=0 := by
          rcases lt_trichotomy (c j) 0 with hj|hj|hj
          · exact False.elim (hU ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
          · exact hj
          · exact False.elim (hL ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
        simpa using hzero j hj


private def LinPoly {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ k : ℕ,∃ a : Fin k → E →ₗ[ℝ] ℝ,∃ b : Fin k → ℝ,S={x | ∀ i,b i≤a i x}

private theorem poly_fintype {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    LinPoly {x | ∀ i,b i≤a i x} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι,fun i => a (e.symm i),fun i => b (e.symm i),?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    exact h _
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (e i)

private theorem poly_preimage {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (S : Set F) (hS : LinPoly S) (f : E →ₗ[ℝ] F) :
    LinPoly (f ⁻¹' S) := by
  obtain ⟨k,a,b,rfl⟩ := hS
  exact ⟨k,fun i => (a i).comp f,b,rfl⟩

private theorem poly_project_scalar {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set (E×ℝ)) (hS : LinPoly S) : LinPoly {x | ∃ t : ℝ,(x,t)∈S} := by
  classical
  obtain ⟨k,a,b,rfl⟩ := hS
  let A := fun i => (a i).comp (LinearMap.inl ℝ E ℝ)
  let c := fun i => a i (0,1)
  let rows : Fin k ⊕ (Fin k×Fin k) → E →ₗ[ℝ] ℝ := Sum.elim
    (fun i => if c i=0 then A i else 0)
    (fun ij => if 0<c ij.1 ∧ c ij.2<0 then (1/c ij.1) • A ij.1-(1/c ij.2) • A ij.2 else 0)
  let rhs : Fin k ⊕ (Fin k×Fin k) → ℝ := Sum.elim
    (fun i => if c i=0 then b i else 0)
    (fun ij => if 0<c ij.1 ∧ c ij.2<0 then b ij.1/c ij.1-b ij.2/c ij.2 else 0)
  have he (i : Fin k) (x : E) (t : ℝ) : a i (x,t)=A i x+c i*t := by
    have hv : (x,t)=(x,0)+t • ((0,1):E×ℝ) := by simp
    rw [hv,map_add,map_smul]
    simp [A,c,mul_comm]
  have hrepr : {x | ∃ t : ℝ,(x,t)∈{z | ∀ i,b i≤a i z}}={x | ∀ i,rhs i≤rows i x} := by
    ext x
    simp only [Set.mem_setOf_eq,he]
    rw [eliminate_scalar]
    constructor
    · rintro ⟨hzero,hpair⟩ i
      rcases i with i|⟨i,j⟩
      · dsimp [rhs,rows]
        split_ifs with hi
        · exact hzero i hi
        · simp
      · dsimp [rhs,rows]
        split_ifs with hij
        · have hh := hpair i j hij.1 hij.2
          simp only [LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
          dsimp [A] at hh ⊢
          simp only [div_eq_mul_inv] at hh ⊢
          nlinarith only [hh]
        · simp
    · intro h
      constructor
      · intro i hi
        have hh := h (Sum.inl i)
        simpa only [rhs,rows,Sum.elim_inl,if_pos hi] using hh
      · intro i j hi hj
        have hh := h (Sum.inr (i,j))
        simp only [rhs,rows,Sum.elim_inr,if_pos (show 0<c i ∧ c j<0 from ⟨hi,hj⟩),LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul] at hh
        simp only [div_eq_mul_inv] at hh ⊢
        nlinarith only [hh]
  rw [hrepr]
  exact poly_fintype rows rhs


private def finSplitMap {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) :
    ((E×(Fin n → ℝ))×ℝ) →ₗ[ℝ] (E×(Fin (n+1) → ℝ)) where
  toFun p := (p.1.1,Fin.cons p.2 p.1.2)
  map_add' := by
    intro p q
    apply Prod.ext
    · rfl
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' := by
    intro c p
    apply Prod.ext
    · rfl
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem poly_project_fin {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (S : Set (E×(Fin n → ℝ))) (hS : LinPoly S) :
    LinPoly {x | ∃ y : Fin n → ℝ,(x,y)∈S} := by
  classical
  induction n with
  | zero =>
    have he : {x | ∃ y : Fin 0 → ℝ,(x,y)∈S}=(LinearMap.inl ℝ E (Fin 0 → ℝ)) ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨y,hy⟩
        have hh : y=0 := Subsingleton.elim _ _
        simpa [hh] using hy
      · intro hx
        exact ⟨0,hx⟩
    rw [he]
    exact poly_preimage S hS _
  | succ n ih =>
    let T := (finSplitMap (E := E) n) ⁻¹' S
    have hT := poly_preimage S hS (finSplitMap (E := E) n)
    have hproj := poly_project_scalar T hT
    have he : {x | ∃ y : Fin (n+1) → ℝ,(x,y)∈S}=
        {x | ∃ z : Fin n → ℝ,(x,z)∈{p | ∃ t : ℝ,(p,t)∈T}} := by
      ext x
      constructor
      · rintro ⟨y,hy⟩
        refine ⟨Fin.tail y,y 0,?_⟩
        simpa [T,finSplitMap,Fin.cons_self_tail] using hy
      · rintro ⟨z,t,ht⟩
        exact ⟨Fin.cons t z,ht⟩
    rw [he]
    exact ih _ hproj


private theorem poly_posW {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : LinPoly (posW W) := by
  classical
  let Y : Fin n → ((Fin m → ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    fun j => (LinearMap.proj j).comp (LinearMap.snd ℝ (Fin m → ℝ) (Fin n → ℝ))
  let R : Fin m → ((Fin m → ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    fun i => (∑ j,W i j • Y j)-(LinearMap.proj i).comp (LinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))
  let rows : Fin n ⊕ (Fin m ⊕ Fin m) → ((Fin m → ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    Sum.elim Y (Sum.elim R (fun i => -R i))
  have hR (i : Fin m) (p : (Fin m → ℝ)×(Fin n → ℝ)) : R i p=(W *ᵥ p.2) i-p.1 i := by
    simp [R,Y,Matrix.mulVec,dotProduct,LinearMap.sum_apply]
  have he : {v | ∃ y : Fin n → ℝ,∀ i,(0:ℝ)≤rows i (v,y)}=posW W := by
    ext v
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨y,fun j => hy (Sum.inl j),?_⟩
      ext i
      have hp := hy (Sum.inr (Sum.inl i))
      have hm := hy (Sum.inr (Sum.inr i))
      change 0≤R i (v,y) at hp
      change 0≤-(R i (v,y)) at hm
      rw [hR] at hp hm
      linarith only [hp,hm]
    · rintro ⟨y,hy,he⟩
      refine ⟨y,?_⟩
      intro i
      rcases i with j|i
      · exact hy j
      · rcases i with i|i
        · change 0≤R i (v,y)
          rw [hR,he]
          simp
        · change 0≤-(R i (v,y))
          rw [hR,he]
          simp
  rw [← he]
  exact poly_project_fin n _ (poly_fintype rows (fun _ => 0))

private theorem poly_affine_preimage {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (S : Set F) (hS : LinPoly S) (f : E →ₗ[ℝ] F) (v : F) :
    LinPoly {x | f x+v∈S} := by
  obtain ⟨k,a,b,rfl⟩ := hS
  refine ⟨k,fun i => (a i).comp f,fun i => b i-a i v,?_⟩
  ext x
  simp only [Set.mem_setOf_eq,map_add,LinearMap.comp_apply]
  constructor
  · intro h i
    have hh := h i
    linarith
  · intro h i
    have hh := h i
    linarith

private theorem poly_to_matrix {n : ℕ} (S : Set (Fin n → ℝ)) (hS : LinPoly S) : IsPolyhedron S := by
  classical
  obtain ⟨k,a,b,rfl⟩ := hS
  refine ⟨k,Matrix.of (fun i j => a i (Pi.single j 1)),b,?_⟩
  have he (x : Fin n → ℝ) : x=∑ j,x j • Pi.single j (1:ℝ) := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  ext x
  have ha (i : Fin k) : a i x=(Matrix.of (fun i j => a i (Pi.single j 1)) *ᵥ x) i := by
    conv_lhs => rw [he x]
    simp [map_sum,map_smul,Matrix.mulVec,dotProduct,mul_comm]
  simp only [Set.mem_setOf_eq,ha]


private theorem poly_iInter {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (S : ι → Set E) (hS : ∀ i,LinPoly (S i)) : LinPoly (⋂ i,S i) := by
  classical
  choose k a b he using hS
  have hh := poly_fintype (fun p : Sigma (fun i => Fin (k i)) => a p.1 p.2)
    (fun p : Sigma (fun i => Fin (k i)) => b p.1 p.2)
  convert! hh using 1
  ext x
  simp only [Set.mem_iInter,he,Set.mem_setOf_eq]
  constructor
  · intro h ⟨i,j⟩
    exact h i j
  · intro h i j
    exact h ⟨i,j⟩

private theorem poly_closed_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) (hS : LinPoly S) : IsClosed S ∧ Convex ℝ S := by
  obtain ⟨k,a,b,rfl⟩ := hS
  have he : {x | ∀ i,b i≤a i x}=⋂ i,(a i) ⁻¹' Set.Ici (b i) := by ext; simp
  rw [he]
  exact ⟨isClosed_iInter (fun i => isClosed_Ici.preimage (a i).continuous_of_finiteDimensional),
    convex_iInter (fun i => (convex_Ici (𝕜 := ℝ) (b i)).linear_preimage (a i))⟩

private theorem poly_K2of {n nb mb : ℕ} (W : Matrix (Fin mb) (Fin nb) ℝ) (ζ : PTSpace n mb) : LinPoly (K2of W ζ) := by
  have hh := poly_affine_preimage (posW W) (poly_posW W) (-(Matrix.of ζ.2).mulVecLin) ζ.1
  convert! hh using 1
  ext x
  simp only [K2of,Set.mem_setOf_eq,LinearMap.neg_apply,Matrix.mulVecLin_apply]
  rw [neg_add_eq_sub]

private theorem K2_closed_convex {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) : IsClosed (K2 μ W) ∧ Convex ℝ (K2 μ W) := by
  exact ⟨isClosed_iInter (fun ζ => isClosed_iInter (fun _ => (poly_closed_convex _ (poly_K2of W ζ)).1)),
    convex_iInter (fun ζ => convex_iInter (fun _ => (poly_closed_convex _ (poly_K2of W ζ)).2))⟩

private theorem K2_poly_of_hull {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hpoly : IsPolyhedralCone (closedPosHull (suppPT μ))) :
    IsPolyhedron (K2 μ W) := by
  classical
  obtain ⟨F,hF⟩ := hpoly
  have hc : IsClosed (PointedCone.hull ℝ (F : Set (PTSpace n mb)) : Set (PTSpace n mb)) := by
    rw [← hF]
    exact isClosed_closure
  have hh : closedPosHull (F : Set (PTSpace n mb))=closedPosHull (suppPT μ) := by
    rw [closedPosHull,hc.closure_eq,← hF]
  have he : K2 μ W=⋂ ζ : F,K2of W ζ := by
    ext x
    simp only [K2,Set.mem_iInter]
    rw [← hull_test W (suppPT μ) x,← hh,hull_test]
    constructor
    · intro h ζ
      exact h ζ ζ.property
    · intro h ζ hζ
      exact h ⟨ζ,hζ⟩
  rw [he]
  exact poly_to_matrix _ (poly_iInter _ (fun ζ : F => poly_K2of W (ζ : PTSpace n mb)))



private def lpEpi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ)×ℝ) :=
  {p | ∃ y : Fin n → ℝ,(∀ j,0≤y j) ∧ A *ᵥ y=p.1 ∧ dotProduct c y≤p.2}

private theorem poly_lpEpi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    LinPoly (lpEpi A c) := by
  classical
  let Y : Fin n → (((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    fun j => (LinearMap.proj j).comp (LinearMap.snd ℝ ((Fin m → ℝ)×ℝ) (Fin n → ℝ))
  let V : (((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) →ₗ[ℝ] (Fin m → ℝ) :=
    (LinearMap.fst ℝ (Fin m → ℝ) ℝ).comp (LinearMap.fst ℝ ((Fin m → ℝ)×ℝ) (Fin n → ℝ))
  let R : Fin m → (((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    fun i => (∑ j,A i j • Y j)-(LinearMap.proj i).comp V
  let O : (((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ (Fin m → ℝ) ℝ).comp (LinearMap.fst ℝ ((Fin m → ℝ)×ℝ) (Fin n → ℝ))-
      ∑ j,c j • Y j
  let rows : Unit ⊕ (Fin n ⊕ (Fin m ⊕ Fin m)) → (((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    Sum.elim (fun _ => O) (Sum.elim Y (Sum.elim R (fun i => -R i)))
  have hR (i : Fin m) (p : ((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) : R i p=(A *ᵥ p.2) i-p.1.1 i := by
    simp [R,Y,V,Matrix.mulVec,dotProduct,LinearMap.sum_apply]
  have hO (p : ((Fin m → ℝ)×ℝ)×(Fin n → ℝ)) : O p=p.1.2-dotProduct c p.2 := by
    simp [O,Y,dotProduct,LinearMap.sum_apply]
  have he : {p | ∃ y : Fin n → ℝ,∀ i,(0:ℝ)≤rows i (p,y)}=lpEpi A c := by
    ext p
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨y,fun j => hy (Sum.inr (Sum.inl j)),?_,?_⟩
      · ext i
        have hp := hy (Sum.inr (Sum.inr (Sum.inl i)))
        have hm := hy (Sum.inr (Sum.inr (Sum.inr i)))
        change 0≤R i (p,y) at hp
        change 0≤-(R i (p,y)) at hm
        rw [hR] at hp hm
        linarith only [hp,hm]
      · have hh := hy (Sum.inl ())
        change 0≤O (p,y) at hh
        rw [hO] at hh
        linarith
    · rintro ⟨y,hy,he,hobj⟩
      refine ⟨y,?_⟩
      intro i
      rcases i with _|i
      · change 0≤O (p,y)
        rw [hO]
        linarith
      · rcases i with j|i
        · exact hy j
        · rcases i with i|i
          · change 0≤R i (p,y)
            rw [hR,he]
            simp
          · change 0≤-(R i (p,y))
            rw [hR,he]
            simp
  rw [← he]
  exact poly_project_fin n _ (poly_fintype rows (fun _ => 0))

private theorem lp_le_of_epi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (t : Fin m → ℝ) (r : ℝ) (hr : (t,r)∈lpEpi A c) : KallMayer.Recourse.LPValue A c t≤(r:EReal) := by
  obtain ⟨y,hy,he,hobj⟩ := hr
  unfold KallMayer.Recourse.LPValue
  apply le_trans (sInf_le ?_) (EReal.coe_le_coe_iff.mpr hobj)
  exact ⟨y,hy,he,rfl⟩

private theorem weak_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (t : Fin m → ℝ) (π : Fin m → ℝ)
    (hπ : ∀ j,(A.transpose *ᵥ π) j≤c j) :
    ((dotProduct π t : ℝ):EReal)≤KallMayer.Recourse.LPValue A c t := by
  apply le_sInf
  rintro r ⟨y,hy,he,rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  rw [← he]
  calc
    dotProduct π (A *ᵥ y) = ∑ j,(A.transpose *ᵥ π) j*y j := by
      simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ dotProduct c y := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hπ j) (hy j))

private theorem lp_optima {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (t : Fin m → ℝ)
    (ht : t∈posW A) (hc : ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤c j) :
    ∃ (y : Fin n → ℝ) (π : Fin m → ℝ), (0 ≤ y) ∧ A *ᵥ y=t ∧
      (∀ j,(A.transpose *ᵥ π) j≤c j) ∧ dotProduct c y=dotProduct π t := by
  classical
  obtain ⟨k,a,b,hepi⟩ := poly_lpEpi A c
  let L := fun i => (a i).comp (LinearMap.inl ℝ (Fin m → ℝ) ℝ)
  let d := fun i => a i (0,1)
  have he (i : Fin k) (s : Fin m → ℝ) (r : ℝ) : a i (s,r)=L i s+d i*r := by
    have hp : (s,r)=(s,0)+r • ((0,1):(Fin m → ℝ)×ℝ) := by simp
    rw [hp,map_add,map_smul]
    simp [L,d,mul_comm]
  have hb (i : Fin k) : b i≤0 := by
    have hh : ((0 : Fin m → ℝ),(0:ℝ))∈lpEpi A c := ⟨0,by simp,by simp,by simp⟩
    rw [hepi] at hh
    simpa only [he,map_zero,mul_zero,add_zero] using hh i
  have hhom (i : Fin k) (s : Fin m → ℝ) (r : ℝ) (hr : (s,r)∈lpEpi A c) : 0≤a i (s,r) := by
    by_contra hn
    have hn : a i (s,r)<0 := lt_of_not_ge hn
    let q := (|b i|+1)/(-a i (s,r))
    have hq : 0≤q := by
      dsimp [q]
      exact div_nonneg (by positivity) (le_of_lt (neg_pos.mpr hn))
    obtain ⟨y,hy,heq,hcost⟩ := hr
    have hh : (q • s,q*r)∈lpEpi A c := by
      refine ⟨q • y,fun j => mul_nonneg hq (hy j),?_,?_⟩
      · simp [Matrix.mulVec_smul,heq]
      · simpa [dotProduct_smul,mul_comm] using mul_le_mul_of_nonneg_left hcost hq
    rw [hepi] at hh
    have hh := hh i
    have heq : (q • s,q*r)=q • (s,r) := rfl
    rw [heq,map_smul] at hh
    change b i≤q*a i (s,r) at hh
    have hv : q*a i (s,r)=-(|b i|+1) := by dsimp [q]; field_simp [ne_of_lt hn] <;> ring
    rw [hv] at hh
    linarith [neg_abs_le (b i)]
  have hd0 (i : Fin k) : 0≤d i := hhom i 0 1 ⟨0,by simp,by simp,by simp⟩
  obtain ⟨π0,hπ0⟩ := hc
  obtain ⟨y0,hy0,hAy0⟩ := ht
  have hbase : (t,dotProduct c y0)∈lpEpi A c := ⟨y0,hy0,hAy0,le_rfl⟩
  have hpos : ∃ i : Fin k,0<d i := by
    by_contra hn
    have hall (r : ℝ) : (t,r)∈lpEpi A c := by
      rw [hepi]
      intro i
      have hd : d i=0 := le_antisymm (le_of_not_gt (fun hi => hn ⟨i,hi⟩)) (hd0 i)
      have hh := hbase
      rw [hepi] at hh
      have hh := hh i
      simpa only [he,hd,zero_mul,add_zero] using hh
    have hh := (weak_dual A c t π0 hπ0).trans (lp_le_of_epi A c t (dotProduct π0 t-1) (hall _))
    have hh := EReal.coe_le_coe_iff.mp hh
    linarith only [hh]
  let J := {i : Fin k // 0<d i}
  haveI : Nonempty J := by obtain ⟨i,hi⟩:=hpos; exact ⟨⟨i,hi⟩⟩
  let P : J → (Fin m → ℝ) := fun i j => -(L i (Pi.single j 1))/d i
  have hP (i : J) (s : Fin m → ℝ) : dotProduct (P i) s=-(L i s)/d i := by
    have hs : s=∑ j,s j • Pi.single j (1:ℝ) := by ext j; simp [Pi.single_apply]
    conv_rhs => rw [hs,map_sum]
    simp only [map_smul,smul_eq_mul,dotProduct,P]
    rw [← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfeas (i : J) : ∀ j,(A.transpose *ᵥ P i) j≤c j := by
    intro j
    have hh : ((fun l => A l j),c j)∈lpEpi A c := by
      refine ⟨Pi.single j 1,?_,?_,?_⟩
      · intro l; simp only [Pi.single_apply]; split_ifs <;> norm_num
      · ext l; simp [Matrix.mulVec,dotProduct,Pi.single_apply]
      · simp [dotProduct,Pi.single_apply]
    have hh := hhom i _ _ hh
    rw [he] at hh
    have hh' : dotProduct (P i) (fun l => A l j)≤c j := by
      rw [hP]
      apply (div_le_iff₀ i.property).mpr
      linarith only [hh]
    simpa [Matrix.mulVec,dotProduct,mul_comm] using hh'
  let r := Finset.univ.sup' Finset.univ_nonempty (fun i : J => dotProduct (P i) t)
  have hr : (t,r)∈lpEpi A c := by
    rw [hepi]
    intro i
    rw [he]
    rcases eq_or_lt_of_le (hd0 i) with hi|hi
    · rw [← hi,zero_mul,add_zero]
      have hh := hbase
      rw [hepi] at hh
      simpa only [he,← hi,zero_mul,add_zero] using hh i
    · let j : J := ⟨i,hi⟩
      have hh : dotProduct (P j) t≤r := Finset.le_sup' (f := fun i : J => dotProduct (P i) t) (Finset.mem_univ _)
      rw [hP] at hh
      have hh := (div_le_iff₀ hi).mp hh
      change -(L i t)≤r*d i at hh
      linarith only [hh,hb i]
  obtain ⟨j,hj,hjr⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : J => dotProduct (P i) t)
  obtain ⟨y,hy,hAy,hcy⟩ := hr
  have hw := (weak_dual A c t (P j) (hfeas j)).trans
    (lp_le_of_epi A c t (dotProduct c y) ⟨y,hy,hAy,le_rfl⟩)
  have hw := EReal.coe_le_coe_iff.mp hw
  refine ⟨y,P j,hy,hAy,hfeas j,le_antisymm ?_ hw⟩
  simpa only [r,hjr] using hcy

private theorem finite_lp {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (c : J → ℝ) (t : I → ℝ)
    (ht : ∃ y : J → ℝ,(∀ j,0 ≤ y j) ∧ ∀ i,∑ j,A i j*y j=t i)
    (hc : ∃ π : I → ℝ,∀ j,∑ i,A i j*π i ≤ c j) :
    ∃ (y : J → ℝ) (π : I → ℝ),(∀ j,0 ≤ y j) ∧
      (∀ i,∑ j,A i j*y j=t i) ∧
      (∀ j,∑ i,A i j*π i ≤ c j) ∧ ∑ j,c j*y j=∑ i,π i*t i := by
  classical
  let e := (Fintype.equivFin I).symm
  let f := (Fintype.equivFin J).symm
  let M : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card J)) ℝ := fun i j => A (e i) (f j)
  obtain ⟨y,π,hy,hAy,hπ,he⟩ := lp_optima M (fun j => c (f j)) (fun i => t (e i)) (by
    obtain ⟨y,hy,ht⟩ := ht
    refine ⟨fun j => y (f j),fun j => hy _,?_⟩
    ext i
    change (∑ j,A (e i) (f j)*y (f j))=t (e i)
    rw [f.sum_comp (fun j => A (e i) j*y j)]
    exact ht (e i)) (by
    obtain ⟨π,hπ⟩ := hc
    refine ⟨fun i => π (e i),?_⟩
    intro j
    change (∑ i,A (e i) (f j)*π (e i)) ≤ c (f j)
    rw [e.sum_comp (fun i => A i (f j)*π i)]
    exact hπ (f j))
  refine ⟨fun j => y (f.symm j),fun i => π (e.symm i),fun j => hy _,?_,?_,?_⟩
  · intro i
    have hh := congrFun hAy (e.symm i)
    change (∑ j,A (e (e.symm i)) (f j)*y j)=t (e (e.symm i)) at hh
    simpa only [Equiv.apply_symm_apply,← f.sum_comp,Equiv.symm_apply_apply] using hh
  · intro j
    have hh := hπ (f.symm j)
    change (∑ i,A (e i) (f (f.symm j))*π i) ≤ c (f (f.symm j)) at hh
    simpa only [Equiv.apply_symm_apply,← e.sum_comp,Equiv.symm_apply_apply] using hh
  · simpa only [dotProduct,← f.sum_comp,← e.sum_comp,Equiv.symm_apply_apply] using he

open SteinitzExchange.Duality

private theorem hull_weights {J V : Type*} [Fintype J] [Fintype V]
    (z : J → V → ℝ) (b : V → ℝ) :
    b ∈ convexHull ℝ (Set.range z) ↔
      ∃ w : J → ℝ,(∀ j,0 ≤ w j) ∧ ∑ j,w j=1 ∧ ∑ j,w j • z j=b := by
  classical
  let S : Set (V → ℝ) := {b | ∃ w : J → ℝ,(∀ j,0 ≤ w j) ∧ ∑ j,w j=1 ∧ ∑ j,w j • z j=b}
  have hs : Convex ℝ S := by
    rintro x ⟨w,hw,hw1,rfl⟩ y ⟨u,hu,hu1,rfl⟩ a d ha hd had
    refine ⟨fun j => a*w j+d*u j,fun j => add_nonneg (mul_nonneg ha (hw j)) (mul_nonneg hd (hu j)),?_,?_⟩
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum,hw1,hu1,mul_one,had]
    · simp only [add_smul,mul_smul,Finset.sum_add_distrib,← Finset.smul_sum]
  constructor
  · apply convexHull_min _ hs
    rintro _ ⟨j,rfl⟩
    refine ⟨Pi.single j 1,?_,?_,?_⟩
    · intro k; simp only [Pi.single_apply]; split_ifs <;> norm_num
    · simp [Pi.single_apply]
    · simp [Pi.single_apply]
  · rintro ⟨w,hw,hw1,he⟩
    exact mem_convexHull_of_exists_fintype w z hw hw1 (fun j => ⟨j,rfl⟩) he

private theorem finite_envelope {J V : Type*} [Fintype J] [Nonempty J] [Fintype V]
    (z : J → V → ℝ) (c : J → ℝ) (b : V → ℝ)
    (hb : b ∈ convexHull ℝ (Set.range z)) :
    ∃ (w : J → ℝ) (p : V → ℝ) (a : ℝ),
      (∀ j,0 ≤ w j) ∧ ∑ j,w j=1 ∧ ∑ j,w j • z j=b ∧
      (∀ j,pairing p (z j)+a ≤ c j) ∧ ∑ j,c j*w j=pairing p b+a := by
  classical
  obtain ⟨w,hw,hw1,hwb⟩ := (hull_weights z b).mp hb
  let A : Option V → J → ℝ := fun i j => match i with | none => 1 | some v => z j v
  let t : Option V → ℝ := fun i => match i with | none => 1 | some v => b v
  obtain ⟨y,π,hy,hAy,hπ,he⟩ := finite_lp A c t (by
    refine ⟨w,hw,?_⟩
    intro i
    cases i with
    | none => simpa [A,t] using hw1
    | some v => simpa [A,t,Finset.sum_apply,smul_eq_mul,mul_comm] using congrFun hwb v) (by
    refine ⟨fun i => match i with | none => ⨅ j,c j | some _ => 0,?_⟩
    intro j
    simpa [A,Fintype.sum_option] using (ciInf_le (Set.finite_range c).bddBelow j))
  refine ⟨y,fun v => π (some v),π none,hy,?_,?_,?_,?_⟩
  · simpa [A,t] using hAy none
  · ext v
    simpa [A,t,Finset.sum_apply,smul_eq_mul,mul_comm] using hAy (some v)
  · intro j
    simpa [A,pairing,Fintype.sum_option,mul_comm,add_comm] using hπ j
  · simpa [t,pairing,Fintype.sum_option,add_comm] using he

private theorem pairing_weights {J V : Type*} [Fintype J] [Fintype V]
    (p : V → ℝ) (w : J → ℝ) (z : J → V → ℝ) :
    pairing p (∑ j,w j • z j)=∑ j,w j*pairing p (z j) := by
  simp only [pairing,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro v hv
  ring

private theorem hull_range {V : Type*} (B : Finset (V → ℤ)) :
    hull B=convexHull ℝ (Set.range (fun x : (B : Set (V → ℤ)) => toReal (x : V → ℤ))) := by
  unfold hull
  congr 1
  ext b
  simp only [Set.mem_image,Set.mem_range,Subtype.exists,exists_prop]

private theorem closure_spec {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (f : (V → ℤ) → ℝ) (b : V → ℝ) (hb : b ∈ hull B) :
    ∃ (w : ↥(B : Set (V → ℤ)) → ℝ) (p : V → ℝ),
      (∀ j,0 ≤ w j) ∧ ∑ j,w j=1 ∧ ∑ j : ↥(B : Set (V → ℤ)),w j • toReal (j : V → ℤ)=b ∧
      convexClosure B f b=∑ j : ↥(B : Set (V → ℤ)),f j*w j ∧
      convexClosure B f b=pairing p b-convexConj B f p := by
  classical
  haveI : Nonempty (B : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB; exact ⟨⟨x,hx⟩⟩
  obtain ⟨w,p,a,hw,hw1,hwb,hp,he⟩ := finite_envelope
    (fun x : (B : Set (V → ℤ)) => toReal (x : V → ℤ)) (fun x => f x) b (by simpa only [hull_range] using hb)
  have hbound (q : V → ℝ) : pairing q b-convexConj B f q ≤ ∑ j : ↥(B : Set (V → ℤ)),f j*w j := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (f := fun j => w j*(pairing q (toReal (j : V → ℤ))-f j))
      (g := fun j => w j*convexConj B f q) (fun j _ => mul_le_mul_of_nonneg_left
        (le_ciSup (Set.finite_range (fun j : (B : Set (V → ℤ)) => pairing q (toReal (j : V → ℤ))-f j)).bddAbove j) (hw j))
    have heq : (∑ j,w j*(pairing q (toReal (j : V → ℤ))-f j))=pairing q b-∑ j : ↥(B : Set (V → ℤ)),f j*w j := by
      rw [← hwb,pairing_weights]
      simp only [mul_sub,Finset.sum_sub_distrib,mul_comm]
    rw [heq,← Finset.sum_mul,hw1,one_mul] at hh
    linarith only [hh]
  have hpC : convexConj B f p ≤ -a := by
    apply ciSup_le
    intro j
    have hh := hp j
    linarith only [hh]
  have heq : pairing p b-convexConj B f p=∑ j : ↥(B : Set (V → ℤ)),f j*w j := by
    apply le_antisymm (hbound p)
    rw [he]
    linarith only [hpC]
  have hc : convexClosure B f b=∑ j : ↥(B : Set (V → ℤ)),f j*w j := by
    apply le_antisymm (ciSup_le hbound)
    rw [← heq]
    exact le_ciSup ⟨_,by rintro _ ⟨q,rfl⟩; exact hbound q⟩ p
  exact ⟨w,p,hw,hw1,hwb,hc,hc.trans heq.symm⟩

private theorem weights_bounds {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (b : V → ℝ) (w : ↥(B : Set (V → ℤ)) → ℝ)
    (hw : ∀ j,0 ≤ w j) (hw1 : ∑ j,w j=1)
    (hwb : ∑ j,w j • toReal (j : V → ℤ)=b) (q : V → ℝ) :
    pairing q b-convexConj B f q ≤ ∑ j : ↥(B : Set (V → ℤ)),f j*w j ∧
    (∑ j : ↥(B : Set (V → ℤ)),f j*w j) ≤ pairing q b-concaveConj B f q := by
  classical
  have heq : (∑ j,w j*(pairing q (toReal (j : V → ℤ))-f j))=pairing q b-∑ j : ↥(B : Set (V → ℤ)),f j*w j := by
    rw [← hwb,pairing_weights]
    simp only [mul_sub,Finset.sum_sub_distrib,mul_comm]
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (f := fun j => w j*(pairing q (toReal (j : V → ℤ))-f j))
      (g := fun j => w j*convexConj B f q) (fun j _ => mul_le_mul_of_nonneg_left
        (le_ciSup (Set.finite_range (fun j : (B : Set (V → ℤ)) => pairing q (toReal (j : V → ℤ))-f j)).bddAbove j) (hw j))
    rw [heq,← Finset.sum_mul,hw1,one_mul] at hh
    linarith only [hh]
  · have hh := Finset.sum_le_sum (s := Finset.univ) (g := fun j => w j*(pairing q (toReal (j : V → ℤ))-f j))
      (f := fun j => w j*concaveConj B f q) (fun j _ => mul_le_mul_of_nonneg_left
        (ciInf_le (Set.finite_range (fun j : (B : Set (V → ℤ)) => pairing q (toReal (j : V → ℤ))-f j)).bddBelow j) (hw j))
    rw [heq,← Finset.sum_mul,hw1,one_mul] at hh
    linarith only [hh]

private theorem closure_weights {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (b : V → ℝ) (w : ↥(B : Set (V → ℤ)) → ℝ)
    (hw : ∀ j,0 ≤ w j) (hw1 : ∑ j,w j=1)
    (hwb : ∑ j,w j • toReal (j : V → ℤ)=b) :
    convexClosure B f b ≤ ∑ j : ↥(B : Set (V → ℤ)),f j*w j ∧
    (∑ j : ↥(B : Set (V → ℤ)),f j*w j) ≤ concaveClosure B f b := by
  exact ⟨ciSup_le (fun q => (weights_bounds B f b w hw hw1 hwb q).1),
    le_ciInf (fun q => (weights_bounds B f b w hw hw1 hwb q).2)⟩

private theorem closure_support {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (b : V → ℝ) (hb : b ∈ hull B) (p : V → ℝ) :
    pairing p b-convexConj B f p ≤ convexClosure B f b ∧
    concaveClosure B f b ≤ pairing p b-concaveConj B f p := by
  classical
  obtain ⟨w,hw,hw1,hwb⟩ := (hull_weights (fun j : (B : Set (V → ℤ)) => toReal (j : V → ℤ)) b).mp (by simpa only [hull_range] using hb)
  exact ⟨le_ciSup ⟨_,by rintro _ ⟨q,rfl⟩;exact (weights_bounds B f b w hw hw1 hwb q).1⟩ p,
    ciInf_le ⟨_,by rintro _ ⟨q,rfl⟩;exact (weights_bounds B f b w hw hw1 hwb q).2⟩ p⟩

private theorem weak_pair {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) (b : V → ℝ) (hb : b ∈ hull B₁ ∩ hull B₂) (p : V → ℝ) :
    concaveClosure B₁ ω b-convexClosure B₂ ζ b ≤ convexConj B₂ ζ p-concaveConj B₁ ω p := by
  have h1 := (closure_support B₁ ω b hb.1 p).2
  have h2 := (closure_support B₂ ζ b hb.2 p).1
  linarith only [h1,h2]

private theorem relaxed_le_dual {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : relaxedValue B₁ B₂ ω ζ ≤ dualValue B₁ B₂ ω ζ := by
  apply iSup_le
  intro b
  apply iSup_le
  intro hb
  apply le_iInf
  intro p
  exact EReal.coe_le_coe_iff.mpr (weak_pair B₁ B₂ ω ζ b hb p)

private theorem strong_feasible {V : Type*} [Fintype V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (ω ζ : (V → ℤ) → ℝ) (hne : (hull B₁ ∩ hull B₂).Nonempty) :
    ∃ b ∈ hull B₁ ∩ hull B₂,∃ p : V → ℝ,
      concaveClosure B₁ ω b-convexClosure B₂ ζ b=convexConj B₂ ζ p-concaveConj B₁ ω p := by
  classical
  haveI : Nonempty (B₁ : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB₁; exact ⟨⟨x,hx⟩⟩
  haveI : Nonempty (B₂ : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB₂; exact ⟨⟨x,hx⟩⟩
  let J₁ := ↥(B₁ : Set (V → ℤ))
  let J₂ := ↥(B₂ : Set (V → ℤ))
  let A : Option (Option V) → J₁ ⊕ J₂ → ℝ := fun i j => match i,j with
    | none,Sum.inl _ => 1
    | none,Sum.inr _ => 0
    | some none,Sum.inl _ => 0
    | some none,Sum.inr _ => 1
    | some (some v),Sum.inl x => -toReal (x : V → ℤ) v
    | some (some v),Sum.inr y => toReal (y : V → ℤ) v
  let c : J₁ ⊕ J₂ → ℝ := Sum.elim (fun x => -ω x) (fun y => ζ y)
  let t : Option (Option V) → ℝ := fun i => match i with
    | none => 1 | some none => 1 | some (some _) => 0
  obtain ⟨b,hb₁,hb₂⟩ := hne
  obtain ⟨w₁,hw₁,hw₁1,hwb₁⟩ := (hull_weights (fun j : J₁ => toReal (j : V → ℤ)) b).mp (by simpa only [hull_range] using hb₁)
  obtain ⟨w₂,hw₂,hw₂1,hwb₂⟩ := (hull_weights (fun j : J₂ => toReal (j : V → ℤ)) b).mp (by simpa only [hull_range] using hb₂)
  obtain ⟨w,π,hw,hAw,hπ,he⟩ := finite_lp A c t (by
    refine ⟨Sum.elim w₁ w₂,?_,?_⟩
    · intro j; cases j with | inl x => exact hw₁ x | inr y => exact hw₂ y
    · intro i
      cases i with
      | none => simpa [A,t,Fintype.sum_sum_type] using hw₁1
      | some i => cases i with
        | none => simpa [A,t,Fintype.sum_sum_type] using hw₂1
        | some v =>
          have h1 := congrFun hwb₁ v
          have h2 := congrFun hwb₂ v
          simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h1 h2
          simp only [A,t,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,neg_mul,Finset.sum_neg_distrib]
          simpa only [mul_comm,h1,h2] using neg_add_cancel (b v)) (by
    let π₀ : Option (Option V) → ℝ := fun i => match i with
      | none => ⨅ x : J₁,-ω x
      | some none => ⨅ y : J₂,ζ y
      | some (some _) => 0
    refine ⟨π₀,?_⟩
    intro j
    cases j with
    | inl x => simpa [A,c,π₀,Fintype.sum_option] using (ciInf_le (Set.finite_range (fun x : J₁ => -ω x)).bddBelow x)
    | inr y => simpa [A,c,π₀,Fintype.sum_option] using (ciInf_le (Set.finite_range (fun y : J₂ => ζ y)).bddBelow y))
  let u : J₁ → ℝ := fun x => w (Sum.inl x)
  let v : J₂ → ℝ := fun y => w (Sum.inr y)
  let b₀ : V → ℝ := ∑ x,u x • toReal (x : V → ℤ)
  let p : V → ℝ := fun j => π (some (some j))
  have hu : ∀ x,0 ≤ u x := fun x => hw _
  have hv : ∀ y,0 ≤ v y := fun y => hw _
  have hu1 : ∑ x,u x=1 := by simpa [u,A,t,Fintype.sum_sum_type] using hAw none
  have hv1 : ∑ y,v y=1 := by simpa [v,A,t,Fintype.sum_sum_type] using hAw (some none)
  have hvb : ∑ y,v y • toReal (y : V → ℤ)=b₀ := by
    ext j
    have hh := hAw (some (some j))
    simp only [A,t,Fintype.sum_sum_type,neg_mul,Finset.sum_neg_distrib] at hh
    simp only [b₀,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,u,v,mul_comm]
    linarith only [hh]
  have hb₀ : b₀ ∈ hull B₁ ∩ hull B₂ := by
    constructor
    · rw [hull_range]
      exact (hull_weights _ b₀).mpr ⟨u,hu,hu1,rfl⟩
    · rw [hull_range]
      exact (hull_weights _ b₀).mpr ⟨v,hv,hv1,hvb⟩
  have hC₁ : π none ≤ concaveConj B₁ ω p := by
    apply le_ciInf
    intro x
    have hh := hπ (Sum.inl x)
    simp only [A,c,Sum.elim_inl,Fintype.sum_option,one_mul,zero_mul,zero_add,neg_mul,Finset.sum_neg_distrib] at hh
    change π none-(∑ j,toReal (x : V → ℤ) j*p j) ≤ -ω x at hh
    have he : pairing p (toReal (x : V → ℤ))=∑ j,toReal (x : V → ℤ) j*p j := by simp only [pairing,mul_comm]
    rw [he]
    linarith only [hh]
  have hC₂ : convexConj B₂ ζ p ≤ -π (some none) := by
    apply ciSup_le
    intro y
    have hh := hπ (Sum.inr y)
    simp only [A,c,Sum.elim_inr,Fintype.sum_option,one_mul,zero_mul,zero_add] at hh
    change π (some none)+(∑ j,toReal (y : V → ℤ) j*p j) ≤ ζ y at hh
    have he : pairing p (toReal (y : V → ℤ))=∑ j,toReal (y : V → ℤ) j*p j := by simp only [pairing,mul_comm]
    rw [he]
    linarith only [hh]
  have hW₁ := (closure_weights B₁ ω b₀ u hu hu1 rfl).2
  have hW₂ := (closure_weights B₂ ζ b₀ v hv hv1 hvb).1
  have he' : -(∑ x : J₁,ω x*u x)+(∑ y : J₂,ζ y*v y)=π none+π (some none) := by
    simpa only [c,t,Fintype.sum_sum_type,Fintype.sum_option,Sum.elim_inl,Sum.elim_inr,neg_mul,Finset.sum_neg_distrib,mul_one,mul_zero,Finset.sum_const_zero,add_zero,u,v] using he
  refine ⟨b₀,hb₀,p,le_antisymm (weak_pair B₁ B₂ ω ζ b₀ hb₀ p) ?_⟩
  linarith only [hC₁,hC₂,hW₁,hW₂,he']

private theorem hull_compact {V : Type*} [Fintype V] (B : Finset (V → ℤ)) : IsCompact (hull B) :=
  ((B.finite_toSet).image toReal).isCompact_convexHull ℝ

private theorem dual_empty {V : Type*} [Fintype V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (ω ζ : (V → ℤ) → ℝ) (hne : ¬(hull B₁ ∩ hull B₂).Nonempty) :
    dualValue B₁ B₂ ω ζ=⊥ := by
  classical
  haveI : Nonempty (B₁ : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB₁; exact ⟨⟨x,hx⟩⟩
  haveI : Nonempty (B₂ : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB₂; exact ⟨⟨x,hx⟩⟩
  have hdis : Disjoint (hull B₂) (hull B₁) := by
    apply Set.disjoint_left.mpr
    intro b h2 h1
    exact hne ⟨b,h1,h2⟩
  obtain ⟨L,u,v,h₂,huv,h₁⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) (hull_compact B₂) (convex_convexHull ℝ _)
    (hull_compact B₁).isClosed hdis
  let p₀ : V → ℝ := fun j => L (Pi.single j 1)
  have hp₀ (b : V → ℝ) : pairing p₀ b=L b := by
    have hb : b=∑ j,b j • Pi.single j (1:ℝ) := by ext j; simp [Pi.single_apply]
    conv_rhs => rw [hb,map_sum]
    simp only [map_smul,smul_eq_mul,pairing,p₀,mul_comm]
  let M : ℝ := ⨆ x : (B₁ : Set (V → ℤ)),ω x
  let m : ℝ := ⨅ y : (B₂ : Set (V → ℤ)),ζ y
  have hM (x : (B₁ : Set (V → ℤ))) : ω x ≤ M := le_ciSup (Set.finite_range (fun x : (B₁ : Set (V → ℤ)) => ω x)).bddAbove x
  have hm (y : (B₂ : Set (V → ℤ))) : m ≤ ζ y := ciInf_le (Set.finite_range (fun y : (B₂ : Set (V → ℤ)) => ζ y)).bddBelow y
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro r
  let s : ℝ := (|M-m-r|+1)/(v-u)
  have hs : 0 ≤ s := div_nonneg (by positivity) (le_of_lt (sub_pos.mpr huv))
  let p := s • p₀
  have hp (b : V → ℝ) : pairing p b=s*L b := by
    dsimp [p]
    simp only [pairing,Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
    exact congrArg (s*·) (hp₀ b)
  have HC : convexConj B₂ ζ p ≤ s*u-m := by
    apply ciSup_le
    intro y
    have hy := (h₂ (toReal (y : V → ℤ)) (subset_convexHull ℝ _ ⟨y,y.property,rfl⟩)).le
    have hh := mul_le_mul_of_nonneg_left hy hs
    rw [hp]
    linarith [hm y]
  have Hc : s*v-M ≤ concaveConj B₁ ω p := by
    apply le_ciInf
    intro x
    have hx := (h₁ (toReal (x : V → ℤ)) (subset_convexHull ℝ _ ⟨x,x.property,rfl⟩)).le
    have hh := mul_le_mul_of_nonneg_left hx hs
    rw [hp]
    linarith [hM x]
  have he : s*(v-u)=|M-m-r|+1 := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr huv)]
  have hlt : convexConj B₂ ζ p-concaveConj B₁ ω p < r := by
    nlinarith only [HC,Hc,he,le_abs_self (M-m-r)]
  exact (iInf_le (fun q : V → ℝ => ((convexConj B₂ ζ q-concaveConj B₁ ω q : ℝ):EReal)) p).trans_lt (EReal.coe_lt_coe_iff.mpr hlt)

private theorem closure_at_point {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (x : V → ℤ) (hx : x ∈ B) :
    convexClosure B f (toReal x) ≤ f x ∧ f x ≤ concaveClosure B f (toReal x) := by
  classical
  constructor
  · apply ciSup_le
    intro p
    have hh := le_ciSup (Set.finite_range (fun j : (B : Set (V → ℤ)) => pairing p (toReal (j : V → ℤ))-f j)).bddAbove ⟨x,hx⟩
    change pairing p (toReal x)-f x ≤ convexConj B f p at hh
    linarith only [hh]
  · apply le_ciInf
    intro p
    have hh := ciInf_le (Set.finite_range (fun j : (B : Set (V → ℤ)) => pairing p (toReal (j : V → ℤ))-f j)).bddBelow ⟨x,hx⟩
    change concaveConj B f p ≤ pairing p (toReal x)-f x at hh
    linarith only [hh]

private theorem primal_le_relaxed {V : Type*} [Fintype V] (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) : primalValue B₁ B₂ ω ζ ≤ relaxedValue B₁ B₂ ω ζ := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx₁
  apply iSup_le
  intro hx₂
  have hb : toReal x ∈ hull B₁ ∩ hull B₂ :=
    ⟨subset_convexHull ℝ _ ⟨x,hx₁,rfl⟩,subset_convexHull ℝ _ ⟨x,hx₂,rfl⟩⟩
  apply le_iSup_of_le (toReal x)
  apply le_iSup_of_le hb
  apply EReal.coe_le_coe_iff.mpr
  have h1 := (closure_at_point B₁ ω x hx₁).2
  have h2 := (closure_at_point B₂ ζ x hx₂).1
  linarith only [h1,h2]

private theorem duality_attainment {V : Type*} [Fintype V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (ω ζ : (V → ℤ) → ℝ) (hne : (hull B₁ ∩ hull B₂).Nonempty) :
    relaxedValue B₁ B₂ ω ζ=dualValue B₁ B₂ ω ζ ∧
    ∃ b ∈ hull B₁ ∩ hull B₂,relaxedValue B₁ B₂ ω ζ=((concaveClosure B₁ ω b-convexClosure B₂ ζ b : ℝ):EReal) := by
  obtain ⟨b,hb,p,he⟩ := strong_feasible B₁ B₂ hB₁ hB₂ ω ζ hne
  have hlo : ((concaveClosure B₁ ω b-convexClosure B₂ ζ b : ℝ):EReal) ≤ relaxedValue B₁ B₂ ω ζ := le_iSup_of_le b (le_iSup_of_le hb le_rfl)
  have hhi : dualValue B₁ B₂ ω ζ ≤ ((concaveClosure B₁ ω b-convexClosure B₂ ζ b : ℝ):EReal) := by
    rw [he]
    exact iInf_le _ p
  have hw := relaxed_le_dual B₁ B₂ ω ζ
  exact ⟨le_antisymm hw (hhi.trans hlo),b,hb,le_antisymm (hw.trans hhi) hlo⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (ω ζ : (V → ℤ) → ℝ) :
    primalValue B₁ B₂ ω ζ ≤ relaxedValue B₁ B₂ ω ζ ∧
    relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ ∧
    ((hull B₁ ∩ hull B₂).Nonempty →
      ∃ b ∈ hull B₁ ∩ hull B₂,
        relaxedValue B₁ B₂ ω ζ = ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal)) := by
  refine ⟨primal_le_relaxed B₁ B₂ ω ζ,?_,fun hn => (duality_attainment B₁ B₂ hB₁ hB₂ ω ζ hn).2⟩
  by_cases hn : (hull B₁ ∩ hull B₂).Nonempty
  · exact (duality_attainment B₁ B₂ hB₁ hB₂ ω ζ hn).1
  · rw [dual_empty B₁ B₂ hB₁ hB₂ ω ζ hn]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    exact (hn ⟨b,hb⟩).elim
