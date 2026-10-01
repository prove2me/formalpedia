-- Prove2me | solution 1 for Wets1974.Feasibility.K2_polyhedron_of_fixed_T
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:19:27.396957+00:00
-- url     : https://prove2.me/submissions/f5c52b06-4468-4c86-83e3-8c5b3d69b1c6

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



private theorem poly_common_rows {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set ι) {k : ℕ} (a : Fin k → E →ₗ[ℝ] ℝ) (b : ι → Fin k → ℝ) :
    LinPoly {x | ∀ ζ ∈ S,∀ i,b ζ i≤a i x} := by
  classical
  by_cases hS : S.Nonempty
  · by_cases hC : ({x : E | ∀ ζ ∈ S,∀ i,b ζ i≤a i x} : Set E).Nonempty
    · obtain ⟨x0,hx0⟩ := hC
      let R := fun i => (fun ζ => b ζ i) '' S
      have hR (i : Fin k) : (R i).Nonempty := hS.image _
      have hb (i : Fin k) : BddAbove (R i) := by
        refine ⟨a i x0,?_⟩
        rintro _ ⟨ζ,hζ,rfl⟩
        exact hx0 ζ hζ i
      refine ⟨k,a,fun i => sSup (R i),?_⟩
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx i
        apply csSup_le (hR i)
        rintro _ ⟨ζ,hζ,rfl⟩
        exact hx ζ hζ i
      · intro hx ζ hζ i
        exact (le_csSup (hb i) ⟨ζ,hζ,rfl⟩).trans (hx i)
    · refine ⟨1,fun _ => 0,fun _ => 1,?_⟩
      ext x
      constructor
      · intro hx
        exact False.elim (hC ⟨x,hx⟩)
      · intro hx
        have hh := hx (0:Fin 1)
        norm_num at hh
  · refine ⟨0,Fin.elim0,Fin.elim0,?_⟩
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _ ζ hζ
      exact False.elim (hS ⟨ζ,hζ⟩)

private theorem K2_fixed_poly {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hT : TFixed μ) : IsPolyhedron (K2 μ W) := by
  classical
  obtain ⟨T0,hT⟩ := hT
  have hc : IsClosed {ζ : PTSpace n mb | Matrix.of ζ.2=T0} :=
    by
      change IsClosed {ζ : PTSpace n mb | ζ.2=(fun i j => T0 i j)}
      exact isClosed_eq continuous_snd continuous_const
  have hae : ∀ᵐ ζ ∂μ.map projPT,Matrix.of ζ.2=T0 :=
    (ae_map_iff measurable_projPT.aemeasurable hc.measurableSet).mpr hT
  have hsupp : ∀ ζ ∈ suppPT μ,Matrix.of ζ.2=T0 :=
    (μ.map projPT).support_subset_of_isClosed hc hae
  obtain ⟨k,a,b,he⟩ := poly_posW W
  let A := fun i => -(a i).comp T0.mulVecLin
  let B := fun ζ : PTSpace n mb => fun i => b i-a i ζ.1
  have hrepr : K2 μ W={x | ∀ ζ ∈ suppPT μ,∀ i,B ζ i≤A i x} := by
    ext x
    simp only [K2,Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro hx ζ hζ i
      have hh := hx ζ hζ
      change ζ.1-Matrix.of ζ.2 *ᵥ x∈posW W at hh
      rw [hsupp ζ hζ,he] at hh
      have hh := hh i
      simp only [map_sub] at hh
      change b i-a i ζ.1≤-(a i (T0 *ᵥ x))
      linarith only [hh]
    · intro hx ζ hζ
      change ζ.1-Matrix.of ζ.2 *ᵥ x∈posW W
      rw [hsupp ζ hζ,he]
      intro i
      have hh := hx ζ hζ i
      change b i-a i ζ.1≤-(a i (T0 *ᵥ x)) at hh
      simp only [map_sub]
      linarith only [hh]
  rw [hrepr]
  exact poly_to_matrix _ (poly_common_rows (suppPT μ) A B)

theorem solution {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hW : W.rank = mb) (hcov : WeakCovariance μ) (hT : TFixed μ) :
    IsClosed (K2 μ W) ∧ Convex ℝ (K2 μ W) ∧ IsPolyhedron (K2 μ W) := by
  exact ⟨(K2_closed_convex μ W).1,(K2_closed_convex μ W).2,K2_fixed_poly μ W hT⟩
