-- Prove2me | solution 1 for Wets1974.Stability.recourse_polyhedral
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:46:13.910218+00:00
-- url     : https://prove2.me/submissions/adf6c32c-ef8e-4b58-875e-dca494eb6ce4

import Definitions.Def_Wets1974_Stability_Model
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

private theorem lp_dual_attained {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (t : Fin m → ℝ)
    (ht : t∈posW A) (hc : ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤c j) :
    ∃ π : Fin m → ℝ,(∀ j,(A.transpose *ᵥ π) j≤c j) ∧
      KallMayer.Recourse.LPValue A c t=((dotProduct π t : ℝ):EReal) := by
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
  refine ⟨P j,hfeas j,le_antisymm ?_ (weak_dual A c t (P j) (hfeas j))⟩
  have hh := lp_le_of_epi A c t r hr
  simpa [r,← hjr] using hh

private theorem lp_poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Wets1974.Stability.IsFiniteConvexPolyhedralOn (fun t => KallMayer.Recourse.LPValue A c t) (Wets1974.Stability.posCone A) ∨
      ∀ t ∈ Wets1974.Stability.posCone A, KallMayer.Recourse.LPValue A c t = ⊥ := by
  classical
  obtain ⟨k,a,b,hepi⟩ := poly_lpEpi A c
  let L := fun i => (a i).comp (LinearMap.inl ℝ (Fin m → ℝ) ℝ)
  let d := fun i => a i (0,1)
  have he (i : Fin k) (t : Fin m → ℝ) (r : ℝ) : a i (t,r)=L i t+d i*r := by
    have hp : (t,r)=(t,0)+r • ((0,1):(Fin m → ℝ)×ℝ) := by simp
    rw [hp,map_add,map_smul]
    simp [L,d,mul_comm]
  have hd0 (i : Fin k) : 0≤d i := by
    by_contra hn
    have hd : d i<0 := lt_of_not_ge hn
    let r := (|b i|+1)/(-d i)
    have hneg : 0 < -d i := neg_pos.mpr hd
    have hr : 0≤r := by dsimp [r]; positivity
    have hh : ((0 : Fin m → ℝ),r)∈lpEpi A c := ⟨0,by simp,by simp,by simpa using hr⟩
    rw [hepi] at hh
    have hh := hh i
    rw [he,map_zero,zero_add] at hh
    have hval : d i*r=-(|b i|+1) := by dsimp [r]; field_simp [ne_of_lt hd] <;> ring
    rw [hval] at hh
    linarith [neg_abs_le (b i)]
  by_cases hpos : ∃ i : Fin k,0<d i
  · let J := {i : Fin k // 0<d i}
    haveI : Nonempty J := by obtain ⟨i,hi⟩:=hpos;exact ⟨⟨i,hi⟩⟩
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := J))
    let e : J ≃ Fin (q+1) := Fintype.equivFinOfCardEq hq
    let F : Fin (q+1) → (Fin m → ℝ) →ᵃ[ℝ] ℝ := fun j =>
      AffineMap.const ℝ (Fin m → ℝ) (b (e.symm j).1/d (e.symm j).1)-
        ((1/d (e.symm j).1) • L (e.symm j).1).toAffineMap
    have hF (j : Fin (q+1)) (t : Fin m → ℝ) : F j t=(b (e.symm j).1-L (e.symm j).1 t)/d (e.symm j).1 := by
      dsimp [F]
      ring
    refine Or.inl ⟨q,F,?_⟩
    intro t ht
    obtain ⟨y0,hy0,hAy0⟩ := ht
    let r := Finset.univ.sup' Finset.univ_nonempty (fun j => F j t)
    have hbase : (t,dotProduct c y0)∈lpEpi A c := ⟨y0,hy0,hAy0,le_rfl⟩
    have hr : (t,r)∈lpEpi A c := by
      rw [hepi]
      intro i
      rw [he]
      rcases eq_or_lt_of_le (hd0 i) with hi|hi
      · rw [← hi,zero_mul,add_zero]
        rw [hepi] at hbase
        have hh := hbase i
        simpa only [he,← hi,zero_mul,add_zero] using hh
      · let j : J := ⟨i,hi⟩
        have hle : F (e j) t≤r := Finset.le_sup' (f := fun j => F j t) (Finset.mem_univ _)
        rw [hF,Equiv.symm_apply_apply] at hle
        have hh := (div_le_iff₀ hi).mp hle
        change b i-L i t≤r*d i at hh
        linarith only [hh]
    apply le_antisymm (lp_le_of_epi A c t r hr)
    apply le_sInf
    rintro v ⟨y,hy,hAy,rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    apply Finset.sup'_le
    intro j hj
    have hh : (t,dotProduct c y)∈lpEpi A c := ⟨y,hy,hAy,le_rfl⟩
    rw [hepi] at hh
    have hh := hh (e.symm j).1
    rw [he] at hh
    rw [hF]
    apply (div_le_iff₀ (e.symm j).2).mpr
    linarith only [hh]
  · refine Or.inr ?_
    intro t ht
    obtain ⟨y0,hy0,hAy0⟩ := ht
    have hall (r : ℝ) : (t,r)∈lpEpi A c := by
      rw [hepi]
      intro i
      have hd : d i=0 := le_antisymm (le_of_not_gt (fun hi => hpos ⟨i,hi⟩)) (hd0 i)
      have hh : (t,dotProduct c y0)∈lpEpi A c := ⟨y0,hy0,hAy0,le_rfl⟩
      rw [hepi] at hh
      have hh := hh i
      simpa only [he,hd,zero_mul,add_zero] using hh
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro r
    exact (lp_le_of_epi A c t (r-1) (hall (r-1))).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))

private theorem lp_concave_poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (t : Fin m → ℝ) (ht : t∈posW A) :
    Wets1974.Stability.IsFiniteConcavePolyhedralOn
      (fun c => KallMayer.Recourse.LPValue A c t)
      {c | ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤c j} := by
  classical
  let I := (Fin m ⊕ Fin m) ⊕ Fin n
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let D : Matrix (Fin n) (Fin (Fintype.card I)) ℝ := fun j k =>
    Sum.elim (Sum.elim (fun i => A i j) (fun i => -A i j)) (fun i => if j=i then 1 else 0) (e.symm k)
  let d : Fin (Fintype.card I) → ℝ := fun k =>
    Sum.elim (Sum.elim (fun i => -t i) (fun i => t i)) (fun _ => 0) (e.symm k)
  let P : (Fin (Fintype.card I) → ℝ) → (Fin m → ℝ) := fun z i => z (e (Sum.inl (Sum.inl i)))-z (e (Sum.inl (Sum.inr i)))
  have hD (z : Fin (Fintype.card I) → ℝ) (j : Fin n) :
      (D *ᵥ z) j=(A.transpose *ᵥ P z) j+z (e (Sum.inr j)) := by
    change (∑ k,D j k*z k)=(∑ i,A i j*P z i)+z (e (Sum.inr j))
    rw [← e.sum_comp]
    change (∑ k : ((Fin m ⊕ Fin m) ⊕ Fin n),D j (e k)*z (e k))=_
    simp only [D,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Fintype.sum_sum_type,Matrix.transpose_apply,P]
    simp only [Finset.sum_add_distrib,mul_sub,Finset.sum_sub_distrib,neg_mul]
    simp [mul_ite,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hd (z : Fin (Fintype.card I) → ℝ) : dotProduct d z= -dotProduct (P z) t := by
    change (∑ k,d k*z k)= -dotProduct (P z) t
    rw [← e.sum_comp]
    change (∑ k : ((Fin m ⊕ Fin m) ⊕ Fin n),d (e k)*z (e k))=_
    simp only [dotProduct,d,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Fintype.sum_sum_type,zero_mul,Finset.sum_const_zero,add_zero,P]
    simp only [sub_mul,Finset.sum_sub_distrib,neg_mul,Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun i hi => mul_comm (t i) (z (e (Sum.inl (Sum.inl i)))))]
    rw [Finset.sum_congr rfl (fun i hi => mul_comm (t i) (z (e (Sum.inl (Sum.inr i)))))]
    ring
  have hz (c : Fin n → ℝ) (π : Fin m → ℝ) (hπ : ∀ j,(A.transpose *ᵥ π) j≤c j) :
      ∃ z : Fin (Fintype.card I) → ℝ,(∀ i,0≤z i) ∧ D *ᵥ z=c ∧ P z=π := by
    let z : Fin (Fintype.card I) → ℝ := fun k =>
      Sum.elim (Sum.elim (fun i => max (π i) 0) (fun i => max (-(π i)) 0))
        (fun j => c j-(A.transpose *ᵥ π) j) (e.symm k)
    have hP : P z=π := by
      ext i
      simp only [P,z,Equiv.symm_apply_apply,Sum.elim_inl]
      rcases le_total 0 (π i) with hi|hi
      · simp [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi)]
      · simp [max_eq_right hi,max_eq_left (neg_nonneg.mpr hi)]
    refine ⟨z,?_,?_,hP⟩
    · intro k
      dsimp [z]
      rcases e.symm k with (i|i)|j
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact sub_nonneg.mpr (hπ j)
    · ext j
      rw [hD,hP]
      simp [z]
  have hvalue (c : Fin n → ℝ) (hc : ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤c j) :
      KallMayer.Recourse.LPValue A c t= -KallMayer.Recourse.LPValue D d c := by
    obtain ⟨π,hπ,hv⟩ := lp_dual_attained A c t ht hc
    obtain ⟨z,hz0,hDz,hPz⟩ := hz c π hπ
    have hdual : KallMayer.Recourse.LPValue D d c=(-(dotProduct π t):ℝ) := by
      apply le_antisymm
      · apply le_trans (lp_le_of_epi D d c _ ⟨z,hz0,hDz,le_rfl⟩)
        change ((dotProduct d z:ℝ):EReal)≤(-(dotProduct π t):ℝ)
        rw [hd,hPz]
      · apply le_sInf
        rintro r ⟨w,hw,hDw,rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        rw [hd]
        have hPw : ∀ j,(A.transpose *ᵥ P w) j≤c j := by
          intro j
          have hh := congrFun hDw j
          rw [hD] at hh
          linarith only [hh,hw (e (Sum.inr j))]
        have hh := weak_dual A c t (P w) hPw
        rw [hv] at hh
        have hh := EReal.coe_le_coe_iff.mp hh
        linarith only [hh]
    rw [hv,hdual]
    simp
  have hdc (c : Fin n → ℝ) (hc : ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤c j) :
      c∈Wets1974.Stability.posCone D := by
    obtain ⟨π,hπ⟩ := hc
    obtain ⟨z,hz0,hDz,hPz⟩ := hz c π hπ
    exact ⟨z,hz0,hDz⟩
  rcases lp_poly D d with hp|hb
  · obtain ⟨k,F,hF⟩ := hp
    dsimp only at hF
    refine ⟨k,fun i => -F i,?_⟩
    intro c hc
    change KallMayer.Recourse.LPValue A c t=_
    rw [hvalue c hc,hF c (hdc c hc),← EReal.coe_neg]
    apply congrArg (fun r : ℝ => (r:EReal))
    apply le_antisymm
    · apply Finset.le_inf'
      intro i hi
      have hh : F i c≤Finset.univ.sup' Finset.univ_nonempty (fun i => F i c) := Finset.le_sup' (f := fun i => F i c) hi
      simpa using neg_le_neg hh
    · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => F i c)
      have hh := Finset.inf'_le (f := fun i => (-F i) c) hi
      rw [he]
      exact hh
  · exfalso
    have hc : ∃ π : Fin m → ℝ,∀ j,(A.transpose *ᵥ π) j≤(0 : Fin n → ℝ) j := ⟨0,by simp⟩
    have hv := hvalue 0 hc
    rw [hb 0 (hdc 0 hc),EReal.neg_bot] at hv
    obtain ⟨y,hy,he⟩ := ht
    have hh := lp_le_of_epi A 0 t 0 ⟨y,hy,he,by simp⟩
    rw [hv] at hh
    exact EReal.coe_ne_top (0:ℝ) (top_le_iff.mp hh)


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


private theorem convex_poly_comp {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (g : F → EReal) (S : Set F) (T : Set E)
    (h : Wets1974.Stability.IsFiniteConvexPolyhedralOn g S) (a : E →ᵃ[ℝ] F)
    (ha : ∀ x∈T,a x∈S) :
    Wets1974.Stability.IsFiniteConvexPolyhedralOn (fun x => g (a x)) T := by
  obtain ⟨k,b,hb⟩ := h
  exact ⟨k,fun i => (b i).comp a,fun x hx => hb (a x) (ha x hx)⟩

open Wets1974.Stability

theorem solution {n nb mb : ℕ} (μ : Measure (Wets1974.Stability.DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) :
    (∀ ξ ∈ μ.support,
      IsFiniteConvexPolyhedralOn (fun x => Wets1974.Stability.Q W x ξ) (Wets1974.Stability.K2 μ W) ∨
        ∀ x ∈ Wets1974.Stability.K2 μ W, Wets1974.Stability.Q W x ξ = ⊥) ∧
    (∀ (x : Fin n → ℝ) (p : Fin mb → ℝ) (T : Matrix (Fin mb) (Fin n) ℝ),
      p - T *ᵥ x ∈ Wets1974.Stability.posW W →
      IsFiniteConcavePolyhedralOn
        (fun q : Fin nb → ℝ => KallMayer.Recourse.PointwiseRecourse W T p q x)
        {q | ∃ π : Fin mb → ℝ, ∀ j, (W.transpose *ᵥ π) j ≤ q j}) ∧
    (∀ (x : Fin n → ℝ) (q : Fin nb → ℝ),
      IsFiniteConvexPolyhedralOn
          (fun ζ : Wets1974.Stability.PTSpace n mb =>
            KallMayer.Recourse.PointwiseRecourse W (Matrix.of ζ.2) ζ.1 q x)
          {ζ | ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ Wets1974.Stability.posW W} ∨
        ∀ ζ : Wets1974.Stability.PTSpace n mb, ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ Wets1974.Stability.posW W →
          KallMayer.Recourse.PointwiseRecourse W (Matrix.of ζ.2) ζ.1 q x = ⊥) := by
  have hs (x : Fin n → ℝ) (hx : x∈Wets1974.Stability.K2 μ W) (ξ : Wets1974.Stability.DataSpace n nb mb)
      (hξ : ξ∈μ.support) : Wets1974.Stability.pOf ξ-Wets1974.Stability.TOf ξ *ᵥ x∈Wets1974.Stability.posCone W := by
    change x∈Wets1974.Feasibility.K2 μ W at hx
    rw [K2_eq_mu,mu_eq_support] at hx
    exact hx ξ hξ
  refine ⟨?_,?_,?_⟩
  · intro ξ hξ
    rcases lp_poly W (Wets1974.Stability.qOf ξ) with hp|hb
    · apply Or.inl
      let a : (Fin n → ℝ) →ᵃ[ℝ] (Fin mb → ℝ) :=
        AffineMap.const ℝ _ (Wets1974.Stability.pOf ξ)-(Wets1974.Stability.TOf ξ).mulVecLin.toAffineMap
      exact convex_poly_comp _ _ _ hp a (fun x hx => hs x hx ξ hξ)
    · exact Or.inr (fun x hx => hb _ (hs x hx ξ hξ))
  · intro x p T ht
    exact lp_concave_poly W (p-T *ᵥ x) ht
  · intro x q
    rcases lp_poly W q with hp|hb
    · exact Or.inl (convex_poly_comp _ _ _ hp (residualMap x).toAffineMap (fun ζ hζ => hζ))
    · exact Or.inr (fun ζ hζ => hb _ hζ)
