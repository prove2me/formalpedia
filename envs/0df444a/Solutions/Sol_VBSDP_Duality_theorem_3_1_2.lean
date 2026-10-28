-- Prove2me | solution 2 for VBSDP.Duality.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:51.065172+00:00
-- url     : https://prove2.me/submissions/d3a772ec-0d1a-49c0-902a-61120e0e166e

import Mathlib
import Definitions.Def_VBSDP_Duality_IsDualFeasible
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_Xopt
import Definitions.Def_VBSDP_Duality_Zopt
import Definitions.Def_VBSDP_Duality_pStar
import Definitions.Def_dualCone
import Theorems.Thm_ConvexOptimization_sdp_strong_duality

-- carved verbatim out of submission 5e632f94-0925-426f-a0bb-e4404446fa6f, lines 1888-1906

section
set_option autoImplicit false
open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix
variable {nn : ℕ}

theorem isSymm_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) (i j : Fin nn) :
    M j i = M i j := congrFun (congrFun h i) j

theorem trace_mul_eq_sum (M N : Matrix (Fin nn) (Fin nn) ℝ) (hN : N.IsSymm) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [isSymm_apply hN i j]

theorem quad_eq_sum (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, M i j * (x i * x j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_mul_sq (P S : Matrix (Fin nn) (Fin nn) ℝ) (hS : S.IsSymm) :
    (P * (S * S)).trace = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) := by
  have hSS : (S * S).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, hS.eq]
  rw [trace_mul_eq_sum P (S * S) hSS]
  have hz : ∀ i j, (S * S) i j = ∑ k, S k i * S k j := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply hS i k]
  calc ∑ i, ∑ j, P i j * (S * S) i j
      = ∑ i, ∑ j, ∑ k, P i j * (S k i * S k j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hz i j, Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ j, P i j * (S k i * S k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, P i j * (S k i * S k j) := Finset.sum_comm
    _ = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) :=
        Finset.sum_congr rfl fun k _ => (quad_eq_sum P (fun i => S k i)).symm

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality

lemma sign_adjusted_lmi {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    -(-F₀ + ∑ i, x i • (-F i)) = lmi F₀ F x := by
  simp [lmi, Finset.sum_neg_distrib, add_comm]

lemma primal_slater_bounded_dual_witness {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (xs : Fin m → ℝ) (hxs : (lmi F₀ F xs).PosDef)
    (hbdd : BddBelow ((fun x : Fin m → ℝ => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, IsDualFeasible F c Z ∧
      -(F₀ * Z).trace = sInf ((fun x : Fin m → ℝ => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) := by
  have hset : {x : Fin m → ℝ | (-(-F₀ + ∑ i, x i • (-F i))).PosSemidef} =
      {x | IsPrimalFeasible F₀ F x} := by
    ext x
    change (-(-F₀ + ∑ i, x i • (-F i))).PosSemidef ↔ (lmi F₀ F x).PosSemidef
    rw [sign_adjusted_lmi]
  obtain ⟨Z, hZ, htrace, hval⟩ := ConvexOptimization.sdp_strong_duality c
    (fun i => -F i) (fun i => (hF i).neg) (-F₀) hF₀.neg xs
    (by simpa only [sign_adjusted_lmi] using hxs) (by simpa only [hset] using hbdd)
  refine ⟨Z, ⟨hZ, ?_⟩, ?_⟩
  · intro i
    have h := htrace i
    simp only [Matrix.neg_mul, Matrix.trace_neg] at h
    linarith
  · simpa only [Matrix.neg_mul, Matrix.trace_neg, hset] using hval

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality
open scoped BigOperators

lemma functional_factors_finite {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (A : E →ₗ[ℝ] (Fin m → ℝ)) (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ z, A z = 0 → f z = 0) :
    ∃ c : Fin m → ℝ, ∀ z, f z = ∑ i, c i * A z i := by
  have hfmem : f ∈ (LinearMap.ker A).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]; exact hf
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hfmem
  obtain ⟨g,hg⟩ := hfmem
  refine ⟨fun i => g (Pi.single i 1), fun z => ?_⟩
  have hz : A z = ∑ i, A z i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  have he : f z = g (A z) := (congrArg (fun l : E →ₗ[ℝ] ℝ => l z) hg).symm
  rw [he]
  conv_lhs => rw [hz,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

def symmetricSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {H | H.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hH hK => hH.add hK
  smul_mem' := fun c _ hH => hH.smul c

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality
open scoped BigOperators
variable {m n : ℕ}

def traceForm (H : Matrix (Fin n) (Fin n) ℝ) : symmetricSpace n →ₗ[ℝ] ℝ where
  toFun Z := (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace
  map_add' := by intros; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' := by intros; simp

def constraints (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    symmetricSpace n →ₗ[ℝ] (Fin m → ℝ) := LinearMap.pi fun i => traceForm (F i)

noncomputable def kernelBasis (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) ℝ (LinearMap.ker (constraints F)) :=
  by
    classical
    letI : Module.Free ℝ (LinearMap.ker (constraints F)) := Module.Free.of_divisionRing ℝ (LinearMap.ker (constraints F))
    exact Module.finBasis ℝ (LinearMap.ker (constraints F))

noncomputable def basisMatrix (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) : Matrix (Fin n) (Fin n) ℝ :=
  ((kernelBasis F a : LinearMap.ker (constraints F)) : symmetricSpace n)

lemma basisMatrix_symm (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) :
    (basisMatrix F a).IsSymm := ((kernelBasis F a : LinearMap.ker (constraints F)) : symmetricSpace n).property

lemma basisMatrix_trace_zero (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) (i : Fin m) :
    (F i * basisMatrix F a).trace = 0 := by
  have h := (kernelBasis F a).property
  exact congrFun h i

lemma exists_kernel_coordinates (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hzero : ∀ i, (F i * H).trace = 0) :
    ∃ t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ,
      H = ∑ a, t a • basisMatrix F a := by
  let Z : LinearMap.ker (constraints F) := ⟨⟨H,hH⟩,funext hzero⟩
  refine ⟨(kernelBasis F).repr Z, ?_⟩
  have h := (kernelBasis F).sum_repr Z
  have he := congrArg (fun z : LinearMap.ker (constraints F) =>
    ((z : symmetricSpace n) : Matrix (Fin n) (Fin n) ℝ)) h
  change H = ∑ a, ((kernelBasis F).repr Z) a • basisMatrix F a
  simpa only [Submodule.coe_sum, Submodule.coe_smul, basisMatrix, Z] using he.symm

lemma trace_pairing_nondegenerate (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hz : ∀ Z : symmetricSpace n, traceForm H Z = 0) : H = 0 := by
  have hself : (H * H).trace = 0 := hz ⟨H,hH⟩
  have he : (H * H).trace = ∑ i, ∑ j, (H i j)^2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : H j i = H i j := congrFun (congrFun hH i) j
    rw [hs,pow_two]
  rw [he] at hself
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (H i j))).mp hself
  ext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (H i j))).mp
    (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa using (sq_eq_zero_iff.mp hj)

lemma kernel_annihilator_span (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i, (F i).IsSymm) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hzero : ∀ a, (H * basisMatrix F a).trace = 0) :
    ∃ c : Fin m → ℝ, H = ∑ i, c i • F i := by
  have hk : ∀ Z : symmetricSpace n, constraints F Z = 0 → traceForm H Z = 0 := by
    intro Z hZ
    obtain ⟨t,ht⟩ := exists_kernel_coordinates F Z Z.property (fun i => congrFun hZ i)
    change (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = 0
    rw [ht,Matrix.mul_sum,Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro a _
    simp [hzero a]
  obtain ⟨c,hc⟩ := functional_factors_finite (constraints F) (traceForm H) hk
  refine ⟨c, ?_⟩
  apply sub_eq_zero.mp
  have hsum : (∑ i, c i • F i).IsSymm := by
    change Matrix.transpose (∑ i, c i • F i) = ∑ i, c i • F i
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
    exact Finset.sum_congr rfl fun i _ => congrArg (fun H => c i • H) (hF i)
  apply trace_pairing_nondegenerate _ (hH.sub hsum)
  intro Z
  change ((H - ∑ i, c i • F i) * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = 0
  rw [Matrix.sub_mul,Matrix.trace_sub,Matrix.sum_mul,Matrix.trace_sum]
  have hh := hc Z
  change (H * (Z : Matrix (Fin n) (Fin n) ℝ)).trace = ∑ i, c i * (F i * (Z : Matrix (Fin n) (Fin n) ℝ)).trace at hh
  simp only [Matrix.smul_mul,Matrix.trace_smul]
  exact sub_eq_zero.mpr hh

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality
variable {m n : ℕ}

lemma trace_lmi_right (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    (lmi F₀ F x * Z).trace = (F₀ * Z).trace + ∑ i, x i * (F i * Z).trace := by
  rw [lmi, Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma trace_lmi_left (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    (Z * lmi F₀ F x).trace = (Z * F₀).trace + ∑ i, x i * (Z * F i).trace := by
  rw [lmi, Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum, Matrix.trace_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma dual_param_constraints (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m → ℝ) (Z₀ : Matrix (Fin n) (Fin n) ℝ)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i)
    (t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :
    ∀ i, (F i * lmi Z₀ (basisMatrix F) t).trace = c i := by
  intro i
  rw [trace_lmi_left, hZ₀ i]
  simp [basisMatrix_trace_zero]

lemma dual_param_surjective (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m → ℝ) (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀s : Z₀.IsSymm)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z) :
    ∃ t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ,
      Z = lmi Z₀ (basisMatrix F) t := by
  have hZs : Z.IsSymm := hZ.1.isHermitian
  have hz : ∀ i, (F i * (Z - Z₀)).trace = 0 := by
    intro i
    rw [Matrix.mul_sub, Matrix.trace_sub, hZ.2 i, hZ₀ i, sub_self]
  obtain ⟨t, ht⟩ := exists_kernel_coordinates F (Z - Z₀) (hZs.sub hZ₀s) hz
  refine ⟨t, ?_⟩
  rw [lmi, ← ht]
  abel

noncomputable def parameterObjective (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :=
  fun a => (F₀ * basisMatrix F a).trace

lemma dual_param_value (F₀ Z₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (t : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) :
    -(F₀ * lmi Z₀ (basisMatrix F) t).trace =
      -(F₀ * Z₀).trace - parameterObjective F₀ F ⬝ᵥ t := by
  rw [trace_lmi_left]
  unfold parameterObjective dotProduct
  rw [neg_add]
  congr 1
  exact congrArg Neg.neg (Finset.sum_congr rfl (fun a _ => mul_comm _ _))

lemma dual_param_value_set (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀s : Z₀.IsSymm)
    (hZ₀ : ∀ i, (F i * Z₀).trace = c i) :
    (fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z} =
      (fun a : ℝ => -(F₀ * Z₀).trace - a) ''
        ((fun t => parameterObjective F₀ F ⬝ᵥ t) ''
          {t | IsPrimalFeasible Z₀ (basisMatrix F) t}) := by
  ext r
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨t, rfl⟩ := dual_param_surjective F c Z₀ hZ₀s hZ₀ Z hZ
    exact ⟨_, ⟨t, hZ.1, rfl⟩, (dual_param_value F₀ Z₀ F t).symm⟩
  · rintro ⟨a, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨lmi Z₀ (basisMatrix F) t, ⟨ht, dual_param_constraints F c Z₀ hZ₀ t⟩,
      dual_param_value F₀ Z₀ F t⟩

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality

lemma sup_sub_image (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A) (k : ℝ) :
    sSup ((fun a => k - a) '' A) = k - sInf A := by
  have hne' : ((fun a => k - a) '' A).Nonempty := hne.image _
  have hb' : BddAbove ((fun a => k - a) '' A) := by
    obtain ⟨b,hb⟩ := hb
    refine ⟨k-b, ?_⟩
    rintro _ ⟨a,ha,rfl⟩
    exact sub_le_sub_left (hb ha) k
  apply le_antisymm
  · apply csSup_le hne'
    rintro _ ⟨a,ha,rfl⟩
    exact sub_le_sub_left (csInf_le hb ha) k
  · have hlow : k - sSup ((fun a => k-a) '' A) ≤ sInf A := by
      apply le_csInf hne
      intro a ha
      have h := le_csSup hb' (show k-a ∈ ((fun a => k-a) '' A) from ⟨a,ha,rfl⟩)
      linarith
    linarith

lemma dual_slater_bounded_primal_witness {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀ : Z₀.PosDef)
    (hZ₀c : ∀ i, (F i * Z₀).trace = c i)
    (hbdd : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    ∃ x : Fin m → ℝ, IsPrimalFeasible F₀ F x ∧
      c ⬝ᵥ x = sSup ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) := by
  have hZ₀s : Z₀.IsSymm := hZ₀.isHermitian
  let A : Set ℝ := (fun t => parameterObjective F₀ F ⬝ᵥ t) ''
    {t | IsPrimalFeasible Z₀ (basisMatrix F) t}
  have hzero : lmi Z₀ (basisMatrix F) (0 : Fin (Module.finrank ℝ (LinearMap.ker (constraints F))) → ℝ) = Z₀ := by
    simp [lmi]
  have hAne : A.Nonempty := by
    refine ⟨_, ⟨0, ?_, rfl⟩⟩
    change (lmi Z₀ (basisMatrix F) 0).PosSemidef
    rw [hzero]
    exact hZ₀.posSemidef
  obtain ⟨b, hb⟩ := hbdd
  have hAbdd : BddBelow A := by
    refine ⟨-(F₀ * Z₀).trace - b, ?_⟩
    rintro a ⟨t, ht, rfl⟩
    have hZt : IsDualFeasible F c (lmi Z₀ (basisMatrix F) t) :=
      ⟨ht, dual_param_constraints F c Z₀ hZ₀c t⟩
    have hh := hb ⟨lmi Z₀ (basisMatrix F) t, hZt, rfl⟩
    change -(F₀ * lmi Z₀ (basisMatrix F) t).trace ≤ b at hh
    rw [dual_param_value] at hh
    linarith
  obtain ⟨Y, hY, hval⟩ := primal_slater_bounded_dual_witness
    (parameterObjective F₀ F) Z₀ (basisMatrix F) hZ₀s (basisMatrix_symm F) 0
    (by simpa only [hzero] using hZ₀) hAbdd
  have hYs : Y.IsSymm := hY.1.isHermitian
  have horth (a : Fin (Module.finrank ℝ (LinearMap.ker (constraints F)))) :
      ((Y - F₀) * basisMatrix F a).trace = 0 := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm Y (basisMatrix F a), hY.2 a]
    simp only [parameterObjective, sub_self]
  obtain ⟨x, hx⟩ := kernel_annihilator_span F hF (Y - F₀) (hYs.sub hF₀) horth
  have hlmi : lmi F₀ F x = Y := by
    rw [lmi, ← hx]
    abel
  have hxval : (lmi F₀ F x * Z₀).trace = (F₀ * Z₀).trace + c ⬝ᵥ x := by
    rw [trace_lmi_right]
    congr 1
    unfold dotProduct
    exact Finset.sum_congr rfl (fun i _ => by rw [hZ₀c i]; ring)
  rw [hlmi, Matrix.trace_mul_comm Y Z₀] at hxval
  have hobj : c ⬝ᵥ x = -(F₀ * Z₀).trace - sInf A := by
    change -(Z₀ * Y).trace = sInf A at hval
    linarith
  refine ⟨x, ?_, ?_⟩
  · change (lmi F₀ F x).PosSemidef
    rw [hlmi]
    exact hY.1
  · rw [dual_param_value_set F₀ F c Z₀ hZ₀s hZ₀c, sup_sub_image A hAne hAbdd]
    exact hobj

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality
open scoped BigOperators MatrixOrder

lemma trace_mul_nonneg {n : ℕ} (P Z : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (P * Z).trace := by
  have hs : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have he : CFC.sqrt Z * CFC.sqrt Z = Z := by
    simpa [sq] using CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
  rw [← he, trace_mul_sq P (CFC.sqrt Z) hs.isHermitian]
  exact Finset.sum_nonneg fun k _ => by simpa using hP.dotProduct_mulVec_nonneg (fun i => CFC.sqrt Z k i)

lemma weak_duality {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    -(F₀ * Z).trace ≤ c ⬝ᵥ x := by
  have hn := trace_mul_nonneg (lmi F₀ F x) Z hx hZ.1
  have he : (lmi F₀ F x * Z).trace = (F₀ * Z).trace + c ⬝ᵥ x := by
    rw [lmi,Matrix.add_mul,Matrix.trace_add,Matrix.sum_mul,Matrix.trace_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.smul_mul,Matrix.trace_smul,hZ.2 i,smul_eq_mul]
    ring
  rw [he] at hn
  linarith

lemma dStar_le_pStar {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    dStar c F₀ F ≤ pStar c F₀ F := by
  apply sSup_le
  rintro a ⟨Z,hZ,rfl⟩
  apply le_sInf
  rintro b ⟨x,hx,rfl⟩
  exact EReal.coe_le_coe (weak_duality c F₀ F x Z hx hZ)

lemma primal_bounds_dual {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (hx : IsPrimalFeasible F₀ F x) :
    BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) := by
  refine ⟨c ⬝ᵥ x, ?_⟩
  rintro b ⟨Z,hZ,rfl⟩
  exact weak_duality c F₀ F x Z hx hZ

lemma dual_bounds_primal {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z) :
    BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) := by
  refine ⟨-(F₀ * Z).trace, ?_⟩
  rintro b ⟨x,hx,rfl⟩
  exact weak_duality c F₀ F x Z hx hZ

end

section
set_option autoImplicit false
open VBSDP
open VBSDP.Duality

lemma ereal_inf_coe (S : Set ℝ) (hne : S.Nonempty) (hb : BddBelow S) :
    sInf ((fun r : ℝ => (r : EReal)) '' S) = (sInf S : ℝ) := by
  let I : EReal := sInf ((fun r : ℝ => (r : EReal)) '' S)
  have hlo : ((sInf S : ℝ) : EReal) ≤ I := by
    apply le_sInf
    rintro _ ⟨r,hr,rfl⟩
    exact EReal.coe_le_coe (csInf_le hb hr)
  obtain ⟨r,hr⟩ := hne
  have hhi : I ≤ (r : EReal) := sInf_le ⟨r,hr,rfl⟩
  have htop : I ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) hhi
  have hbot : I ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (sInf S)) hlo
  have he := EReal.coe_toReal htop hbot
  have ht : I.toReal ≤ sInf S := by
    apply le_csInf ⟨r,hr⟩
    intro s hs
    apply EReal.coe_le_coe_iff.mp
    rw [he]
    exact sInf_le ⟨s,hs,rfl⟩
  apply le_antisymm _ hlo
  rw [← he]
  exact EReal.coe_le_coe ht

lemma ereal_sup_coe (S : Set ℝ) (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun r : ℝ => (r : EReal)) '' S) = (sSup S : ℝ) := by
  let I : EReal := sSup ((fun r : ℝ => (r : EReal)) '' S)
  have hhi : I ≤ ((sSup S : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨r,hr,rfl⟩
    exact EReal.coe_le_coe (le_csSup hb hr)
  obtain ⟨r,hr⟩ := hne
  have hlo : (r : EReal) ≤ I := le_sSup ⟨r,hr,rfl⟩
  have htop : I ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top (sSup S)) hhi
  have hbot : I ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot r) hlo
  have he := EReal.coe_toReal htop hbot
  have ht : sSup S ≤ I.toReal := by
    apply csSup_le ⟨r,hr⟩
    intro s hs
    apply EReal.coe_le_coe_iff.mp
    rw [he]
    exact le_sSup ⟨s,hs,rfl⟩
  apply le_antisymm hhi
  rw [← he]
  exact EReal.coe_le_coe ht

lemma ereal_inf_coe_unbounded (S : Set ℝ) (h : ¬ BddBelow S) :
    sInf ((fun r : ℝ => (r : EReal)) '' S) = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  obtain ⟨s,hs,hsr⟩ := not_bddBelow_iff.mp h r
  exact lt_of_le_of_lt (sInf_le ⟨s,hs,rfl⟩) (EReal.coe_lt_coe_iff.mpr hsr)

lemma ereal_sup_coe_unbounded (S : Set ℝ) (h : ¬ BddAbove S) :
    sSup ((fun r : ℝ => (r : EReal)) '' S) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  obtain ⟨s,hs,hrs⟩ := not_bddAbove_iff.mp h r
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hrs) (le_sSup ⟨s,hs,rfl⟩)

lemma pStar_eq_coe_inf {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hne : ∃ x, IsPrimalFeasible F₀ F x)
    (hb : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = (sInf ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x}) : ℝ) := by
  have hi := ereal_inf_coe ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})
    (by obtain ⟨x,hx⟩ := hne; exact ⟨_,x,hx,rfl⟩) hb
  simpa only [Set.image_image,pStar,dStar] using hi

lemma dStar_eq_coe_sup {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hne : ∃ Z, IsDualFeasible F c Z)
    (hb : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    dStar c F₀ F = (sSup ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z}) : ℝ) := by
  have hi := ereal_sup_coe ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})
    (by obtain ⟨Z,hZ⟩ := hne; exact ⟨_,Z,hZ,rfl⟩) hb
  simpa only [Set.image_image,pStar,dStar] using hi

lemma primal_unbounded_values {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hb : ¬ BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = ⊥ ∧ dStar c F₀ F = ⊥ := by
  have hp : pStar c F₀ F = ⊥ := by
    simpa only [Set.image_image,pStar,dStar] using ereal_inf_coe_unbounded _ hb
  refine ⟨hp, ?_⟩
  exact le_bot_iff.mp (hp ▸ dStar_le_pStar c F₀ F)

lemma dual_unbounded_values {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hb : ¬ BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    pStar c F₀ F = ⊤ ∧ dStar c F₀ F = ⊤ := by
  have hd : dStar c F₀ F = ⊤ := by
    simpa only [Set.image_image,pStar,dStar] using ereal_sup_coe_unbounded _ hb
  exact ⟨top_le_iff.mp (hd ▸ dStar_le_pStar c F₀ F),hd⟩

lemma dual_optimal_of_value {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : IsDualFeasible F c Z)
    (hv : ((-(F₀ * Z).trace : ℝ) : EReal) = pStar c F₀ F) :
    pStar c F₀ F = dStar c F₀ F ∧ Z ∈ Zopt c F₀ F := by
  have hl : ((-(F₀ * Z).trace : ℝ) : EReal) ≤ dStar c F₀ F := le_sSup ⟨Z,hZ,rfl⟩
  have he : pStar c F₀ F = dStar c F₀ F := le_antisymm (hv ▸ hl) (dStar_le_pStar c F₀ F)
  exact ⟨he,hZ,hv.trans he⟩

lemma primal_optimal_of_value {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (hx : IsPrimalFeasible F₀ F x)
    (hv : ((c ⬝ᵥ x : ℝ) : EReal) = dStar c F₀ F) :
    pStar c F₀ F = dStar c F₀ F ∧ x ∈ Xopt c F₀ F := by
  have hl : pStar c F₀ F ≤ ((c ⬝ᵥ x : ℝ) : EReal) := sInf_le ⟨x,hx,rfl⟩
  have he : pStar c F₀ F = dStar c F₀ F := le_antisymm (hv ▸ hl) (dStar_le_pStar c F₀ F)
  exact ⟨he,hx,hv.trans he.symm⟩

lemma primal_slater_optimal_of_bounded {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (xs : Fin m → ℝ) (hxs : (lmi F₀ F xs).PosDef)
    (hbdd : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})) :
    pStar c F₀ F = dStar c F₀ F ∧ (Zopt c F₀ F).Nonempty := by
  obtain ⟨Z, hZ, hval⟩ := primal_slater_bounded_dual_witness c F₀ F hF₀ hF xs hxs hbdd
  have hp := pStar_eq_coe_inf c F₀ F ⟨xs, hxs.posSemidef⟩ hbdd
  have hv : ((-(F₀ * Z).trace : ℝ) : EReal) = pStar c F₀ F := by rw [hp, hval]
  have ho := dual_optimal_of_value c F₀ F Z hZ hv
  exact ⟨ho.1, Z, ho.2⟩

lemma dual_slater_optimal_of_bounded {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsSymm) (hF : ∀ i, (F i).IsSymm)
    (Z₀ : Matrix (Fin n) (Fin n) ℝ) (hZ₀ : Z₀.PosDef)
    (hZ₀c : ∀ i, (F i * Z₀).trace = c i)
    (hbdd : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})) :
    pStar c F₀ F = dStar c F₀ F ∧ (Xopt c F₀ F).Nonempty := by
  obtain ⟨x, hx, hval⟩ := dual_slater_bounded_primal_witness c F₀ F hF₀ hF Z₀ hZ₀ hZ₀c hbdd
  have hd := dStar_eq_coe_sup c F₀ F ⟨Z₀, hZ₀.posSemidef, hZ₀c⟩ hbdd
  have hv : ((c ⬝ᵥ x : ℝ) : EReal) = dStar c F₀ F := by rw [hd, hval]
  have ho := primal_optimal_of_value c F₀ F x hx hv
  exact ⟨ho.1, x, ho.2⟩

theorem theorem_3_1 {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian) :
    (((∃ x, (lmi F₀ F x).PosDef) ∨
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      pStar c F₀ F = dStar c F₀ F) ∧
    (((∃ x, (lmi F₀ F x).PosDef) ∧
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      (Xopt c F₀ F).Nonempty ∧ (Zopt c F₀ F).Nonempty) := by
  have hF₀s : F₀.IsSymm := hF₀
  have hFs : ∀ i, (F i).IsSymm := hF
  constructor
  · rintro (⟨xs, hxs⟩ | ⟨Z₀, hZ₀, hZ₀c⟩)
    · by_cases hb : BddBelow ((fun x => c ⬝ᵥ x) '' {x | IsPrimalFeasible F₀ F x})
      · exact (primal_slater_optimal_of_bounded c F₀ F hF₀s hFs xs hxs hb).1
      · have hu := primal_unbounded_values c F₀ F hb
        exact hu.1.trans hu.2.symm
    · by_cases hb : BddAbove ((fun Z => -(F₀ * Z).trace) '' {Z | IsDualFeasible F c Z})
      · exact (dual_slater_optimal_of_bounded c F₀ F hF₀s hFs Z₀ hZ₀ hZ₀c hb).1
      · have hu := dual_unbounded_values c F₀ F hb
        exact hu.1.trans hu.2.symm
  · rintro ⟨⟨xs, hxs⟩, ⟨Z₀, hZ₀, hZ₀c⟩⟩
    have hp := dual_bounds_primal c F₀ F Z₀ ⟨hZ₀.posSemidef, hZ₀c⟩
    have hd := primal_bounds_dual c F₀ F xs hxs.posSemidef
    exact ⟨(dual_slater_optimal_of_bounded c F₀ F hF₀s hFs Z₀ hZ₀ hZ₀c hd).2,
      (primal_slater_optimal_of_bounded c F₀ F hF₀s hFs xs hxs hp).2⟩

end

section
set_option autoImplicit false
open VBSDP.Duality

theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian) :
    (((∃ x, (lmi F₀ F x).PosDef) ∨
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      pStar c F₀ F = dStar c F₀ F) ∧
    (((∃ x, (lmi F₀ F x).PosDef) ∧
      (∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosDef ∧ ∀ i, (F i * Z).trace = c i)) →
      (Xopt c F₀ F).Nonempty ∧ (Zopt c F₀ F).Nonempty) := by
  exact theorem_3_1 c F₀ F hF₀ hF

end
