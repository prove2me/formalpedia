-- Prove2me | solution 1 for Wets1974.Feasibility.K2_eq_feasibility_sets
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:38:01.271515+00:00
-- url     : https://prove2.me/submissions/29a675be-cead-4fec-81f6-3b3c7a203bd3

import Mathlib.MeasureTheory.Integral.IntegrableOn
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


private theorem cone_coeff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) :
    ∃ B : ℝ,0<B ∧ ∀ a : ι → ℝ,(∀ i,0≤a i) →
      ∃ b : ι → ℝ,(∀ i,0≤b i) ∧ (∑ i,b i • c i)=(∑ i,a i • c i) ∧
        ∀ i,|b i|≤B*‖∑ i,a i • c i‖ := by
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
  refine ⟨b,?_,hbeq.trans heq',?_⟩
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


private theorem feasible_cost_bound {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ (t : Fin m → ℝ) (q : Fin n → ℝ),t∈posW W →
      KallMayer.Recourse.LPValue W q t≤((B*∑ j,∑ i,|q j*t i| : ℝ):EReal) := by
  obtain ⟨B,hB,hbound⟩ := cone_coeff_bound (fun j : Fin n => (fun i : Fin m => W i j))
  have hsum (a : Fin n → ℝ) : (∑ j,a j • (fun i => W i j))=W *ᵥ a := by
    ext i
    simp [Finset.sum_apply,Matrix.mulVec,dotProduct,mul_comm]
  refine ⟨B,hB,?_⟩
  intro t q ht
  obtain ⟨a,ha,hat⟩ := ht
  obtain ⟨b,hb,hbe,hbn⟩ := hbound a ha
  simp only [hsum,hat] at hbe hbn
  have htn : ‖t‖≤∑ i,|t i| := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
  have hdot : dotProduct q b≤B*∑ j,∑ i,|q j*t i| := by
    calc
      _ ≤ ∑ j,|q j| *|b j| := Finset.sum_le_sum (fun j _ => by simpa only [abs_mul] using le_abs_self (q j*b j))
      _ ≤ ∑ j,|q j| *(B*‖t‖) := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbn j) (abs_nonneg _))
      _ ≤ ∑ j,|q j| *(B*(∑ i,|t i|)) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htn hB.le) (abs_nonneg _))
      _ = _ := by
        simp only [abs_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold KallMayer.Recourse.LPValue
  apply le_trans (sInf_le ?_) (EReal.coe_le_coe_iff.mpr hdot)
  exact ⟨b,hb,hbe,rfl⟩


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

theorem solution {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hW : W.rank = mb) (hcov : WeakCovariance μ) :
    K2 μ W = K2supp μ W ∧ K2supp μ W = K2mu μ W ∧ K2mu μ W = K2s μ W := by
  exact ⟨(K2_eq_mu μ W).trans (mu_eq_support μ W), (mu_eq_support μ W).symm,
    Set.Subset.antisymm (mu_subset_strong μ W hcov) (strong_subset_mu μ W)⟩
