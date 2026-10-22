-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_projective_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:42:08.212506+00:00
-- url     : https://prove2.me/submissions/f803b64e-e9af-4f5a-9afc-5fabc75c86fc

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04
noncomputable section

set_option synthInstance.maxSize 8192

open QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]



theorem g66s_pair_norm (x : X) (y : Y) :
    ∏ b, ‖pair x y b‖ = ‖x‖ * ‖y‖ := by
  rw [Fintype.prod_bool, mul_comm]
  rfl

/-- The bilinear map (x, y) ↦ x ⊗ y on the algebraic tensor product. -/
noncomputable def g66s_β : X →ₗ[K] Y →ₗ[K] Algebraic K X Y :=
  LinearMap.mk₂ K (fun x y => PiTensorProduct.tprod K (pair x y))
    (fun x x' y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (x + x'), e x, e x']
      exact (PiTensorProduct.tprod K).map_update_add (pair 0 y) false (ULift.up x) (ULift.up x'))
    (fun c x y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (c • x), e x]
      exact (PiTensorProduct.tprod K).map_update_smul (pair 0 y) false c (ULift.up x))
    (fun x y y' => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (y + y'), e y, e y']
      exact (PiTensorProduct.tprod K).map_update_add (pair x 0) true (ULift.up y) (ULift.up y'))
    (fun c x y => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (c • y), e y]
      exact (PiTensorProduct.tprod K).map_update_smul (pair x 0) true c (ULift.up y))

theorem g66s_β_apply (x : X) (y : Y) : g66s_β (K := K) x y = PiTensorProduct.tprod K (pair x y) := rfl

def G66sRep (u : Algebraic K X Y) (r : ℝ) : Prop :=
  ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
    u = ∑ i, PiTensorProduct.tprod K (pair (x i) (y i)) ∧ r = ∑ i, ‖x i‖ * ‖y i‖

theorem g66s_rep_zero : G66sRep (K := K) (X := X) (Y := Y) 0 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, by simp⟩

theorem g66s_rep_add {u u' : Algebraic K X Y} {r r' : ℝ} (h : G66sRep u r) (h' : G66sRep u' r') :
    G66sRep (u + u') (r + r') := by
  obtain ⟨n, x, y, rfl, rfl⟩ := h
  obtain ⟨m, x', y', rfl, rfl⟩ := h'
  refine ⟨n + m, Fin.append x x', Fin.append y y', ?_, ?_⟩
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem g66s_rep_single (c : K) (m : (b : Bool) → Factors X Y b) :
    G66sRep (c • PiTensorProduct.tprod K m) (‖c‖ * ∏ b, ‖m b‖) := by
  refine ⟨1, fun _ => c • (m false).down, fun _ => (m true).down, ?_, ?_⟩
  · simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [← g66s_β_apply, map_smul, LinearMap.smul_apply, g66s_β_apply]
    congr 2
    funext b; cases b <;> rfl
  · simp only [Finset.univ_unique, Finset.sum_singleton, norm_smul, Fintype.prod_bool]
    show ‖c‖ * (‖(m true).down‖ * ‖(m false).down‖) = _
    ring

theorem g66s_rep_lift (p : FreeAddMonoid (K × ((b : Bool) → Factors X Y b))) :
    G66sRep ((p.toList.map fun q => q.1 • PiTensorProduct.tprod K q.2).sum)
      (PiTensorProduct.projectiveSeminormAux p) := by
  simp only [PiTensorProduct.projectiveSeminormAux]
  induction p.toList with
  | nil => simpa using g66s_rep_zero
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact g66s_rep_add (g66s_rep_single q.1 q.2) ih

/-- Finite representations have cost at least the norm, and the norm is approached. -/
theorem g66s_cost (u : Algebraic K X Y) :
    (finiteCosts u).Nonempty ∧ BddBelow (finiteCosts u) ∧ ‖u‖ = sInf (finiteCosts u) := by
  classical
  have hlift : ∀ p ∈ PiTensorProduct.lifts u,
      PiTensorProduct.projectiveSeminormAux p ∈ finiteCosts u := by
    intro p hp
    rw [PiTensorProduct.mem_lifts_iff] at hp
    have := g66s_rep_lift p
    rw [hp] at this
    obtain ⟨n, x, y, h1, h2⟩ := this
    exact ⟨n, x, y, h1, h2⟩
  have hcost : ∀ r ∈ finiteCosts u, ‖u‖ ≤ r := by
    rintro r ⟨n, x, y, hu, rfl⟩
    let p : FreeAddMonoid (K × ((b : Bool) → Factors X Y b)) :=
      FreeAddMonoid.ofList (List.ofFn fun i => ((1 : K), pair (x i) (y i)))
    have hp : p ∈ PiTensorProduct.lifts u := by
      rw [PiTensorProduct.mem_lifts_iff, hu]
      simp [p, FreeAddMonoid.toList_ofList, List.map_ofFn, List.sum_ofFn]
    have hc : PiTensorProduct.projectiveSeminormAux p = ∑ i, ‖x i‖ * ‖y i‖ := by
      simp only [PiTensorProduct.projectiveSeminormAux, p, FreeAddMonoid.toList_ofList, List.map_ofFn,
        List.sum_ofFn]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.comp_apply, norm_one, one_mul]
      exact g66s_pair_norm _ _
    rw [← hc, PiTensorProduct.norm_def]
    exact ciInf_le (PiTensorProduct.bddBelow_projectiveSemiNormAux _) ⟨p, hp⟩
  obtain ⟨p0, hp0⟩ := PiTensorProduct.nonempty_lifts u
  refine ⟨⟨_, hlift p0 hp0⟩, ⟨0, fun r hr => (norm_nonneg u).trans (hcost r hr)⟩, ?_⟩
  apply le_antisymm
  · exact le_csInf ⟨_, hlift p0 hp0⟩ hcost
  · rw [PiTensorProduct.norm_def]
    exact le_ciInf fun p => csInf_le ⟨0, fun r hr => (norm_nonneg u).trans (hcost r hr)⟩ (hlift p.1 p.2)

noncomputable def g66s_L (f : X →L[K] K) (g : Y →L[K] K) : (b : Bool) → Factors X Y b →ₗ[K] K
  | false => f.toLinearMap.comp (ULift.moduleEquiv (R := K) (M := X)).toLinearMap
  | true => g.toLinearMap.comp (ULift.moduleEquiv (R := K) (M := Y)).toLinearMap

noncomputable def g66s_V (f : X →L[K] K) (g : Y →L[K] K) : Algebraic K X Y →ₗ[K] K :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K Bool K).compLinearMap (g66s_L f g))

theorem g66s_V_pair (f : X →L[K] K) (g : Y →L[K] K) (x : X) (y : Y) :
    g66s_V f g (PiTensorProduct.tprod K (pair x y)) = f x * g y := by
  simp only [g66s_V, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fintype.prod_bool]
  rw [mul_comm]
  rfl

theorem g66s_V_le (f : X →L[K] K) (g : Y →L[K] K) (u : Algebraic K X Y) :
    ∀ r ∈ finiteCosts u, ‖g66s_V f g u‖ ≤ ‖f‖ * ‖g‖ * r := by
  rintro r ⟨n, x, y, rfl, rfl⟩
  rw [map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [g66s_V_pair, norm_mul]
  calc ‖f (x i)‖ * ‖g (y i)‖ ≤ (‖f‖ * ‖x i‖) * (‖g‖ * ‖y i‖) :=
        mul_le_mul (f.le_opNorm _) (g.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = ‖f‖ * ‖g‖ * (‖x i‖ * ‖y i‖) := by ring

theorem g66s_V_zero (f : X →L[K] K) (g : Y →L[K] K) (u : Algebraic K X Y) (hu : ‖u‖ = 0) :
    g66s_V f g u = 0 := by
  obtain ⟨hne, hbdd, hinf⟩ := g66s_cost u
  rw [← norm_le_zero_iff]
  by_contra hpos
  push_neg at hpos
  set C := ‖f‖ * ‖g‖ + 1
  have hC : 0 < C := by positivity
  have hlt : sInf (finiteCosts u) < ‖g66s_V f g u‖ / C := by
    rw [← hinf, hu]; positivity
  obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt hne hlt
  have h1 := g66s_V_le f g u r hr
  have hr0 : 0 ≤ r := by
    obtain ⟨n, x, y, _, rfl⟩ := hr
    exact Finset.sum_nonneg fun i _ => by positivity
  have : ‖g66s_V f g u‖ ≤ C * r := h1.trans (by nlinarith [norm_nonneg f, norm_nonneg g])
  rw [lt_div_iff₀ hC] at hrlt
  linarith

/-- The projective seminorm on the algebraic tensor product is a norm. -/
theorem g66s_sep (u : Algebraic K X Y) (hu : ‖u‖ = 0) : u = 0 := by
  classical
  obtain ⟨⟨r0, n, x, y, hxy, -⟩, -, -⟩ := g66s_cost u
  let X0 : Submodule K X := Submodule.span K (Set.range x)
  haveI : FiniteDimensional K X0 := FiniteDimensional.span_of_finite K (Set.finite_range x)
  let b0 := Module.finBasis K X0
  have hφ : ∀ j, ∃ f : X →L[K] K, ∀ v : X0, f v = b0.coord j v := by
    intro j
    obtain ⟨f, hf, -⟩ := exists_extension_norm_eq X0
      (LinearMap.toContinuousLinearMap (b0.coord j))
    exact ⟨f, fun v => hf v⟩
  choose f hf using hφ
  have hx : ∀ i, x i = ∑ j, f j (x i) • (b0 j : X) := by
    intro i
    have hmem : x i ∈ X0 := Submodule.subset_span ⟨i, rfl⟩
    have := b0.sum_repr ⟨x i, hmem⟩
    have h2 := congrArg Subtype.val this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j ⟨x i, hmem⟩]
    rfl
  let w : Fin (Module.finrank K X0) → Y := fun j => ∑ i, f j (x i) • y i
  have hu' : u = ∑ j, PiTensorProduct.tprod K (pair (b0 j : X) (w j)) := by
    rw [hxy]
    simp_rw [← g66s_β_apply]
    conv_lhs => arg 2; ext i; rw [hx i]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, w]
    rw [Finset.sum_comm]
  by_cases hw : ∀ j, w j = 0
  · rw [hu']; simp [hw, ← g66s_β_apply]
  · push_neg at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨g, -, hg⟩ := exists_dual_vector K (w j) (norm_ne_zero_iff.2 hj)
    have h0 := g66s_V_zero (f j) g u hu
    rw [hxy, map_sum] at h0
    simp only [g66s_V_pair] at h0
    have : g (w j) = ∑ i, f j (x i) * g (y i) := by
      simp [w, map_sum, map_smul, smul_eq_mul]
    rw [← this, hg] at h0
    exact absurd (by exact_mod_cast h0) (norm_ne_zero_iff.2 hj)
theorem g66r_dense : DenseRange (algebraicInclusion (K := K) (X := X) (Y := Y)) := by
  have h1 : DenseRange (fun u : NormedAlgebraic K X Y => (u : Projective K X Y)) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (SeparationQuotient.mk : Algebraic K X Y → NormedAlgebraic K X Y) :=
    SeparationQuotient.surjective_mk.denseRange
  exact h1.comp h2 (UniformSpace.Completion.continuous_coe _)

theorem g66r_unif : IsUniformInducing (algebraicInclusion (K := K) (X := X) (Y := Y)) := by
  have h1 : IsUniformInducing (fun u : NormedAlgebraic K X Y => (u : Projective K X Y)) :=
    UniformSpace.Completion.isUniformInducing_coe _
  have h2 : IsUniformInducing (SeparationQuotient.mk : Algebraic K X Y → NormedAlgebraic K X Y) :=
    SeparationQuotient.isUniformInducing_mk
  exact h1.comp h2

theorem g66r_norm (u : Algebraic K X Y) : ‖algebraicInclusion (K := K) (X := X) (Y := Y) u‖ = ‖u‖ := by
  show ‖((SeparationQuotient.mk u : NormedAlgebraic K X Y) : Projective K X Y)‖ = ‖u‖
  rw [UniformSpace.Completion.norm_coe, SeparationQuotient.norm_mk]

theorem g66r_ext_eq (B : Bilinear K X Y Z) (u : Algebraic K X Y) :
    extendBilinear B (algebraicInclusion u) = PiTensorProduct.liftIsometry K (Factors X Y) Z B u :=
  ContinuousLinearMap.extend_eq _ g66r_dense g66r_unif u

theorem g66r_ext_tprod (B : Bilinear K X Y Z) (m : (b : Bool) → Factors X Y b) :
    extendBilinear B (algebraicInclusion (PiTensorProduct.tprod K m)) = B m := by
  rw [g66r_ext_eq, PiTensorProduct.liftIsometry_apply_apply, PiTensorProduct.lift.tprod]
  rfl

theorem g66r_ext_pure (B : Bilinear K X Y Z) (x : X) (y : Y) :
    extendBilinear B (pure x y) = B (pair x y) :=
  g66r_ext_tprod B (pair x y)

theorem g66r_uniq (L1 L2 : Projective K X Y →L[K] Z) (h : ∀ x y, L1 (pure x y) = L2 (pure x y)) :
    L1 = L2 := by
  have hc : L1.comp algebraicInclusion = L2.comp algebraicInclusion := by
    apply ContinuousLinearMap.coe_injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    have hm : m = pair (m false).down (m true).down := by
      funext b; cases b <;> rfl
    rw [hm]
    exact h _ _
  rw [← ContinuousLinearMap.extend_unique (L1.comp algebraicInclusion) g66r_dense g66r_unif L1 rfl,
    ← ContinuousLinearMap.extend_unique (L2.comp algebraicInclusion) g66r_dense g66r_unif L2 rfl, hc]

theorem g66r_ext_norm (B : Bilinear K X Y Z) : ‖extendBilinear B‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  refine g66r_dense.induction_on z (isClosed_le (by fun_prop) (by fun_prop)) fun u => ?_
  rw [g66r_ext_eq, g66r_norm]
  calc ‖PiTensorProduct.liftIsometry K (Factors X Y) Z B u‖
      ≤ ‖PiTensorProduct.liftIsometry K (Factors X Y) Z B‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖B‖ * ‖u‖ := by rw [LinearIsometryEquiv.norm_map]

theorem g66r_incl_norm : ‖algebraicInclusion (K := K) (X := X) (Y := Y)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by rw [g66r_norm, one_mul]

theorem g66r_res_norm (L : Projective K X Y →L[K] Z) : ‖restrictBilinear L‖ ≤ ‖L‖ := by
  have : restrictBilinear L = (PiTensorProduct.liftIsometry K (Factors X Y) Z).symm
      (L.comp algebraicInclusion) := rfl
  rw [this, LinearIsometryEquiv.norm_map]
  calc ‖L.comp algebraicInclusion‖ ≤ ‖L‖ * ‖algebraicInclusion (K := K) (X := X) (Y := Y)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * 1 := by gcongr; exact g66r_incl_norm
    _ = ‖L‖ := mul_one _

theorem g66s_pure_eq (x : X) (y : Y) : pure (K := K) x y = algebraicInclusion (g66s_β x y) := rfl

theorem g66s_pure_norm_le (x : X) (y : Y) : ‖pure (K := K) x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [g66s_pure_eq, g66r_norm, g66s_β_apply, ← g66s_pair_norm]
  exact PiTensorProduct.projectiveSeminorm_tprod_le _

theorem g66s_bal1 (a : X) (b : Y) : ∃ (a' : X) (b' : Y), g66s_β (K := K) a' b' = g66s_β a b ∧
    ‖a'‖ = Real.sqrt (‖a‖ * ‖b‖) ∧ ‖b'‖ = Real.sqrt (‖a‖ * ‖b‖) := by
  by_cases h : a = 0 ∨ b = 0
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · rcases h with h | h <;> simp [h]
    · rcases h with h | h <;> simp [h]
    · rcases h with h | h <;> simp [h]
  · push_neg at h
    obtain ⟨ha, hb⟩ := h
    have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
    set s : ℝ := Real.sqrt (‖b‖ / ‖a‖) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hnb hna)
    refine ⟨((s : ℝ) : K) • a, ((s⁻¹ : ℝ) : K) • b, ?_, ?_, ?_⟩
    · rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← RCLike.ofReal_mul,
        inv_mul_cancel₀ hs0.ne', RCLike.ofReal_one, one_smul]
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hs0, eq_comm,
        Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
      have h2 : s * s = ‖b‖ / ‖a‖ := Real.mul_self_sqrt (div_pos hnb hna).le
      calc s * ‖a‖ * (s * ‖a‖) = (s * s) * (‖a‖ * ‖a‖) := by ring
        _ = ‖a‖ * ‖b‖ := by rw [h2]; field_simp
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hs0), eq_comm,
        Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
      have h2 : s * s = ‖b‖ / ‖a‖ := Real.mul_self_sqrt (div_pos hnb hna).le
      calc s⁻¹ * ‖b‖ * (s⁻¹ * ‖b‖) = (s * s)⁻¹ * (‖b‖ * ‖b‖) := by rw [mul_inv]; ring
        _ = ‖a‖ * ‖b‖ := by rw [h2]; field_simp

/-- Balanced finite representations with cost close to the norm. -/
theorem g66s_frep (u : Algebraic K X Y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (a : Fin n → X) (b : Fin n → Y),
      u = ∑ i, PiTensorProduct.tprod K (pair (a i) (b i)) ∧
      ∑ i, ‖a i‖ * ‖b i‖ < ‖u‖ + δ ∧
      ∀ i, ‖a i‖ ^ 2 ≤ ‖u‖ + δ ∧ ‖b i‖ ^ 2 ≤ ‖u‖ + δ := by
  classical
  obtain ⟨hne, -, hinf⟩ := g66s_cost u
  have hlt : sInf (finiteCosts u) < ‖u‖ + δ := by rw [← hinf]; linarith
  obtain ⟨r, ⟨n, a, b, hu, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne hlt
  have hb1 := fun i => g66s_bal1 (K := K) (a i) (b i)
  choose a' b' hab ha' hb' using hb1
  have hcost : ∀ i, ‖a' i‖ * ‖b' i‖ = ‖a i‖ * ‖b i‖ := by
    intro i
    rw [ha', hb', Real.mul_self_sqrt (by positivity)]
  have hle : ∀ i, ‖a i‖ * ‖b i‖ ≤ ∑ j, ‖a j‖ * ‖b j‖ :=
    fun i => Finset.single_le_sum (f := fun j => ‖a j‖ * ‖b j‖) (fun j _ => by positivity)
      (Finset.mem_univ i)
  refine ⟨n, a', b', ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hu]; simp_rw [← g66s_β_apply, hab]
  · simp_rw [hcost]; exact hr
  · rw [ha', Real.sq_sqrt (by positivity)]; linarith [hle i]
  · rw [hb', Real.sq_sqrt (by positivity)]; linarith [hle i]

theorem g66s_approx (z : Projective K X Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ (x : ℕ → X) (y : ℕ → Y), TensorRep z x y ∧ ∑' n, ‖x n‖ * ‖y n‖ < ‖z‖ + ε := by
  classical
  set δ : ℕ → ℝ := fun k => ε / 4 / 2 / 2 ^ k with hδdef
  have hδ : ∀ k, 0 < δ k := fun k => by positivity
  have hδsum : HasSum δ (ε / 4) := hasSum_geometric_two' (ε / 4)
  have hu : ∀ k, ∃ u : Algebraic K X Y, ‖z - algebraicInclusion u‖ < δ k := fun k => by
    obtain ⟨u, hu⟩ := Metric.denseRange_iff.1 g66r_dense z (δ k) (hδ k)
    exact ⟨u, by rwa [dist_eq_norm] at hu⟩
  choose u hu using hu
  let d : ℕ → Algebraic K X Y := fun k => Nat.casesOn k (u 0) (fun k => u (k + 1) - u k)
  have hd0 : ‖d 0‖ ≤ ‖z‖ + δ 0 := by
    show ‖u 0‖ ≤ _
    rw [← g66r_norm]
    have := norm_sub_norm_le (algebraicInclusion (K := K) (X := X) (Y := Y) (u 0)) z
    rw [norm_sub_rev] at this
    linarith [hu 0]
  have hdk : ∀ k, ‖d (k + 1)‖ ≤ δ (k + 1) + δ k := by
    intro k
    show ‖u (k + 1) - u k‖ ≤ _
    rw [← g66r_norm, map_sub]
    calc ‖algebraicInclusion (u (k + 1)) - algebraicInclusion (u k)‖
        = ‖(z - algebraicInclusion (u k)) - (z - algebraicInclusion (u (k + 1)))‖ := by congr 1; abel
      _ ≤ ‖z - algebraicInclusion (u k)‖ + ‖z - algebraicInclusion (u (k + 1))‖ := norm_sub_le _ _
      _ ≤ δ (k + 1) + δ k := by linarith [hu k, hu (k + 1)]
  -- bound sequence e k ≥ cost of the k-th block
  let e : ℕ → ℝ := fun k => ‖d k‖ + δ k
  have he0 : e 0 ≤ ‖z‖ + 2 * δ 0 := by simp only [e]; linarith
  have hek : ∀ k, e (k + 1) ≤ 2 * δ (k + 1) + δ k := fun k => by simp only [e]; linarith [hdk k]
  have hesum : Summable e := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun k => by simp only [e]; positivity) hek ?_
    exact (((summable_nat_add_iff 1).2 hδsum.summable).mul_left 2).add hδsum.summable
  have hetsum : ∑' k, e k ≤ ‖z‖ + 3 * (ε / 4) := by
    rw [hesum.tsum_eq_zero_add]
    have h1 : ∑' k, e (k + 1) ≤ ∑' k, (2 * δ (k + 1) + δ k) :=
      Summable.tsum_le_tsum hek ((summable_nat_add_iff 1).2 hesum)
        ((((summable_nat_add_iff 1).2 hδsum.summable).mul_left 2).add hδsum.summable)
    have h2 : ∑' k, (2 * δ (k + 1) + δ k) = 2 * (ε / 4 - δ 0) + ε / 4 := by
      rw [Summable.tsum_add (((summable_nat_add_iff 1).2 hδsum.summable).mul_left 2)
        hδsum.summable, tsum_mul_left, hδsum.tsum_eq]
      have := hδsum.summable.tsum_eq_zero_add
      rw [hδsum.tsum_eq] at this
      have h3 : ∑' k, δ (k + 1) = ε / 4 - δ 0 := by linarith
      rw [h3]
    linarith
  have hδle : ∀ k, δ k ≤ ε / 8 := by
    intro k
    simp only [hδdef]
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have heb : ∀ k, e k ≤ ‖z‖ + ε := by
    intro k
    cases k with
    | zero => linarith [he0, hδle 0, norm_nonneg z]
    | succ k => linarith [hek k, hδle k, hδle (k + 1), norm_nonneg z]
  have hfr := fun k => g66s_frep (d k) (δ k) (hδ k)
  choose n a b hdrep hcost hbd using hfr
  let F : ℕ × ℕ → X := fun p => if h : p.2 < n p.1 then a p.1 ⟨p.2, h⟩ else 0
  let G : ℕ × ℕ → Y := fun p => if h : p.2 < n p.1 then b p.1 ⟨p.2, h⟩ else 0
  set C := Real.sqrt (‖z‖ + ε) with hC
  have hFb : ∀ p, ‖F p‖ ≤ C ∧ ‖G p‖ ≤ C := by
    intro p
    simp only [F, G]
    split_ifs with h
    · constructor
      · rw [hC, Real.le_sqrt (norm_nonneg _) (by positivity)]
        exact (hbd p.1 _).1.trans (heb p.1)
      · rw [hC, Real.le_sqrt (norm_nonneg _) (by positivity)]
        exact (hbd p.1 _).2.trans (heb p.1)
    · simp only [norm_zero]; exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩
  let c : ℕ × ℕ → ℝ := fun p => ‖F p‖ * ‖G p‖
  have hc0 : ∀ p, 0 ≤ c p := fun p => by positivity
  have hsupp : ∀ k j, j ∉ Finset.range (n k) → F (k, j) = 0 ∧ G (k, j) = 0 := by
    intro k j hj
    simp only [Finset.mem_range] at hj
    simp [F, G, hj]
  have hfibc : ∀ k, HasSum (fun j => c (k, j)) (∑ i, ‖a k i‖ * ‖b k i‖) := by
    intro k
    have h : HasSum (fun j => c (k, j)) (∑ j ∈ Finset.range (n k), c (k, j)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by simp [c, (hsupp k j hj).1])
    convert h using 1
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [c, F, G, i.2]
  have hcs : Summable c := by
    rw [summable_prod_of_nonneg hc0]
    refine ⟨fun k => (hfibc k).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun j => hc0 _) (fun k => ?_) hesum
    rw [(hfibc k).tsum_eq]; exact (hcost k).le
  have hctsum : ∑' p, c p ≤ ‖z‖ + 3 * (ε / 4) := by
    rw [hcs.tsum_prod' (fun k => (hfibc k).summable)]
    refine le_trans ?_ hetsum
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ hesum
    · rw [(hfibc k).tsum_eq]; exact (hcost k).le
    · exact hcs.prod
  let f : ℕ × ℕ → Projective K X Y := fun p => pure (F p) (G p)
  have hfn : ∀ p, ‖f p‖ ≤ c p := fun p => g66s_pure_norm_le _ _
  have hfs : Summable f := Summable.of_norm_bounded hcs hfn
  have hfib : ∀ k, HasSum (fun j => f (k, j)) (algebraicInclusion (d k)) := by
    intro k
    have h : HasSum (fun j => f (k, j)) (∑ j ∈ Finset.range (n k), f (k, j)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by
        simp only [f, (hsupp k j hj).1, (hsupp k j hj).2, g66s_pure_eq, map_zero,
          LinearMap.zero_apply])
    convert h using 1
    rw [Finset.sum_range, hdrep k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f, F, G, i.2, g66s_pure_eq, g66s_β_apply]
  have hds : Summable fun k => algebraicInclusion (K := K) (X := X) (Y := Y) (d k) :=
    Summable.of_norm_bounded hesum (fun k => by rw [g66r_norm]; simp only [e]; linarith [hδ k])
  have htel : ∀ K', ∑ k ∈ Finset.range (K' + 1), d k = u K' := by
    intro K'
    induction K' with
    | zero => simp [d]
    | succ K' ih => rw [Finset.sum_range_succ, ih]; simp [d]
  have hdz : HasSum (fun k => algebraicInclusion (K := K) (X := X) (Y := Y) (d k)) z := by
    rw [hds.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    have : (fun K' => ∑ k ∈ Finset.range (K' + 1), algebraicInclusion (K := K) (X := X) (Y := Y) (d k)) =
        fun K' => algebraicInclusion (u K') := by
      funext K'; rw [← map_sum, htel]
    rw [this, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun K' => ?_) hδsum.summable.tendsto_atTop_zero
    rw [norm_sub_rev]; exact (hu K').le
  have hfz : HasSum f z := by
    have h1 := hfs.hasSum
    rw [hfs.tsum_prod' (fun k => (hfib k).summable)] at h1
    have h2 : (fun k => ∑' j, f (k, j)) = fun k => algebraicInclusion (d k) :=
      funext fun k => (hfib k).tsum_eq
    rw [h2, hdz.tsum_eq] at h1
    exact h1
  let eq := Nat.pairEquiv
  refine ⟨fun m => F (eq.symm m), fun m => G (eq.symm m), ⟨⟨C, fun m => hFb _⟩, ?_, ?_⟩, ?_⟩
  · exact (Equiv.summable_iff eq.symm (f := c)).2 hcs
  · exact (Equiv.hasSum_iff eq.symm (f := f)).2 hfz
  · have : ∑' m, ‖F (eq.symm m)‖ * ‖G (eq.symm m)‖ = ∑' p, c p := Equiv.tsum_eq eq.symm c
    rw [this]
    linarith

theorem g66s_lower (z : Projective K X Y) : ∀ r ∈ tensorCosts z, ‖z‖ ≤ r := by
  rintro r ⟨x, y, ⟨-, hs, hz⟩, rfl⟩
  have hs' : Summable fun n => ‖pure (K := K) (x n) (y n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => g66s_pure_norm_le _ _) hs
  rw [← hz.tsum_eq]
  exact (norm_tsum_le_tsum_norm hs').trans
    (Summable.tsum_le_tsum (fun n => g66s_pure_norm_le _ _) hs' hs)

theorem g66s_normalize (x : X) (y : Y) (v0 : X) (w0 : Y) (hv0 : ‖v0‖ = 1) (hw0 : ‖w0‖ = 1) :
    ∃ (x' : X) (y' : Y), ‖x'‖ = 1 ∧ ‖y'‖ = 1 ∧
      ((‖x‖ * ‖y‖ : ℝ) : K) • pure (K := K) x' y' = pure x y := by
  by_cases h : x = 0 ∨ y = 0
  · refine ⟨v0, w0, hv0, hw0, ?_⟩
    rcases h with h | h <;> simp [h, g66s_pure_eq]
  · push_neg at h
    obtain ⟨hx, hy⟩ := h
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    refine ⟨((‖x‖⁻¹ : ℝ) : K) • x, ((‖y‖⁻¹ : ℝ) : K) • y, ?_, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hx)), inv_mul_cancel₀ hnx]
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hy)), inv_mul_cancel₀ hny]
    · simp only [g66s_pure_eq, map_smul, LinearMap.smul_apply, smul_smul]
      rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
      have : ‖x‖ * ‖y‖ * (‖y‖⁻¹ * ‖x‖⁻¹) = 1 := by field_simp
      rw [this, RCLike.ofReal_one, one_smul]

theorem g66s_V_bound (f : X →L[K] K) (g : Y →L[K] K) (u : Algebraic K X Y) :
    ‖g66s_V f g u‖ ≤ ‖f‖ * ‖g‖ * ‖u‖ := by
  obtain ⟨hne, -, hinf⟩ := g66s_cost u
  rw [hinf]
  by_cases hC : ‖f‖ * ‖g‖ = 0
  · have := g66s_V_le f g u _ hne.some_mem
    rw [hC, zero_mul] at this ⊢
    exact this
  · have hCp : 0 < ‖f‖ * ‖g‖ := lt_of_le_of_ne (by positivity) (Ne.symm hC)
    rw [← div_le_iff₀' hCp]
    exact le_csInf hne fun r hr => by
      rw [div_le_iff₀' hCp]; exact g66s_V_le f g u r hr

theorem g66s_cross (x : X) (y : Y) : ‖pure (K := K) x y‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm (g66s_pure_norm_le x y)
  by_cases h : x = 0 ∨ y = 0
  · rcases h with h | h <;> simp [h]
  push_neg at h
  obtain ⟨f, hf1, hfx⟩ := exists_dual_vector K x (norm_ne_zero_iff.2 h.1)
  obtain ⟨g, hg1, hgy⟩ := exists_dual_vector K y (norm_ne_zero_iff.2 h.2)
  have hb := g66s_V_bound f g (g66s_β x y)
  rw [g66s_β_apply, g66s_V_pair, hfx, hgy, hf1, hg1, one_mul, one_mul, ← RCLike.ofReal_mul,
    RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at hb
  rw [g66s_pure_eq, g66r_norm, g66s_β_apply]
  exact hb

theorem g66t_one_of (c : K) (hc : ‖c‖ ≤ 1) (hre : RCLike.re c = 1) : c = 1 := by
  have h2 : ‖c‖ ^ 2 = RCLike.re c ^ 2 + RCLike.im c ^ 2 := by
    rw [RCLike.norm_sq_eq_def]; ring
  have him : RCLike.im c = 0 := by
    have : ‖c‖ ^ 2 ≤ 1 := by
      calc ‖c‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
        _ = 1 := one_pow 2
    rw [h2, hre] at this
    nlinarith [sq_nonneg (RCLike.im c)]
  apply RCLike.ext <;> simp [hre, him]

/-- The key step: a norm-one functional attaining the norm on a representation with total
cost ‖z‖ equals one on every term. -/
theorem g66t_key (z : Projective K X Y) (a : ℕ → ℝ) (x : ℕ → X) (y : ℕ → Y)
    (ha : ∀ n, 0 < a n) (hs : Summable a) (hu : ∀ n, ‖x n‖ = 1 ∧ ‖y n‖ = 1)
    (hz : HasSum (fun n => (a n : K) • pure (x n) (y n)) z) (heq : ‖z‖ = ∑' n, a n)
    (φ : Projective K X Y →L[K] K) (hφ : ‖φ‖ ≤ 1) (hφz : φ z = (‖z‖ : K)) :
    ∀ n, φ (pure (x n) (y n)) = 1 := by
  set c : ℕ → K := fun n => φ (pure (x n) (y n)) with hcdef
  have hc1 : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    calc ‖c n‖ ≤ ‖φ‖ * ‖pure (K := K) (x n) (y n)‖ := φ.le_opNorm _
      _ ≤ 1 * 1 := by
        rw [g66s_cross, (hu n).1, (hu n).2, mul_one, mul_one]
        exact hφ
      _ = 1 := one_mul 1
  have hre1 : ∀ n, RCLike.re (c n) ≤ 1 := fun n => (RCLike.re_le_norm _).trans (hc1 n)
  have hφs : HasSum (fun n => (a n : K) * c n) (φ z) := by
    have := φ.hasSum hz
    simpa [hcdef, map_smul, smul_eq_mul] using this
  have hres : HasSum (fun n => a n * RCLike.re (c n)) (RCLike.re (φ z)) := by
    have := (RCLike.reCLM (K := K)).hasSum hφs
    simpa [RCLike.re_ofReal_mul] using this
  rw [hφz, RCLike.ofReal_re, heq] at hres
  have hdiff : HasSum (fun n => a n * (1 - RCLike.re (c n))) 0 := by
    have := hs.hasSum.sub hres
    simp only [sub_self] at this
    refine this.congr_fun ?_
    intro n; ring
  have hnn : ∀ n, 0 ≤ a n * (1 - RCLike.re (c n)) :=
    fun n => mul_nonneg (ha n).le (sub_nonneg.2 (hre1 n))
  have hzero := (hasSum_zero_iff_of_nonneg hnn).1 hdiff
  intro n
  have h1 := congrFun hzero n
  have hre : RCLike.re (c n) = 1 := by
    have := (mul_eq_zero.1 h1).resolve_left (ha n).ne'
    linarith
  exact g66t_one_of _ (hc1 n) hre

theorem g66t_ext_res (L : Projective K X Y →L[K] Z) : extendBilinear (restrictBilinear L) = L := by
  apply g66r_uniq
  intro x y
  rw [g66r_ext_pure]
  show L (algebraicInclusion (PiTensorProduct.tprodL K (pair x y))) = L (pure x y)
  rw [PiTensorProduct.tprodL_toFun]
  rfl

theorem g66t_res_pair (L : Projective K X Y →L[K] Z) (x : X) (y : Y) :
    restrictBilinear L (pair x y) = L (pure x y) := by
  rw [← g66r_ext_pure, g66t_ext_res]

theorem g66t_norm_ge (G : Bilinear K X Y Z) (x : X) (y : Y) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖G (pair x y)‖ ≤ ‖G‖ := by
  have := G.le_opNorm (pair x y)
  rwa [g66s_pair_norm, hx, hy, mul_one, mul_one] at this

theorem g67m_pure_add (a b : X) (y : Y) : pure (K := K) (a + b) y = pure a y + pure b y := by
  rw [g66s_pure_eq, g66s_pure_eq, g66s_pure_eq, LinearMap.map_add₂, map_add]

theorem g67m_pure_add' (x : X) (a b : Y) : pure (K := K) x (a + b) = pure x a + pure x b := by
  rw [g66s_pure_eq, g66s_pure_eq, g66s_pure_eq, map_add, map_add]

theorem g67m_pure_sub (a b : X) (y : Y) : pure (K := K) (a - b) y = pure a y - pure b y := by
  rw [g66s_pure_eq, g66s_pure_eq, g66s_pure_eq, LinearMap.map_sub₂, map_sub]

theorem g67m_pure_sub' (x : X) (a b : Y) : pure (K := K) x (a - b) = pure x a - pure x b := by
  rw [g66s_pure_eq, g66s_pure_eq, g66s_pure_eq, map_sub, map_sub]

theorem g67m_pure_smul (c : K) (x : X) (y : Y) : pure (K := K) (c • x) y = c • pure (K := K) x y := by
  rw [g66s_pure_eq, g66s_pure_eq, LinearMap.map_smul₂, map_smul]

theorem g67m_pure_smul' (c : K) (x : X) (y : Y) : pure (K := K) x (c • y) = c • pure (K := K) x y := by
  rw [g66s_pure_eq, g66s_pure_eq, map_smul, map_smul]

/-- the bilinear map (x, y) ↦ A x ⊗ B y -/
noncomputable def g67mBil (A : X →L[K] X) (B : Y →L[K] Y) : Bilinear K X Y (Projective K X Y) :=
  MultilinearMap.mkContinuous
    { toFun := fun m => pure (A (m false).down) (B (m true).down)
      map_update_add' := by
        intro _ m i p q
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change pure (A (p.down + q.down)) (B (m true).down) =
            pure (A p.down) (B (m true).down) + pure (A q.down) (B (m true).down)
          rw [map_add, g67m_pure_add]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change pure (A (m false).down) (B (p.down + q.down)) =
            pure (A (m false).down) (B p.down) + pure (A (m false).down) (B q.down)
          rw [map_add, g67m_pure_add']
      map_update_smul' := by
        intro _ m i c p
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change pure (A (c • p.down)) (B (m true).down) = c • pure (A p.down) (B (m true).down)
          rw [map_smul, g67m_pure_smul]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change pure (A (m false).down) (B (c • p.down)) = c • pure (A (m false).down) (B p.down)
          rw [map_smul, g67m_pure_smul'] }
    (‖A‖ * ‖B‖) (by
      intro m
      change ‖pure (K := K) (A (m false).down) (B (m true).down)‖ ≤ ‖A‖ * ‖B‖ * ∏ i : Bool, ‖m i‖
      simp only [Fintype.prod_bool]
      change _ ≤ ‖A‖ * ‖B‖ * (‖(m true).down‖ * ‖(m false).down‖)
      rw [g66s_cross]
      calc ‖A (m false).down‖ * ‖B (m true).down‖ ≤ (‖A‖ * ‖(m false).down‖) * (‖B‖ * ‖(m true).down‖) :=
            mul_le_mul (A.le_opNorm _) (B.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = _ := by ring)

theorem g67m_bil_apply (A : X →L[K] X) (B : Y →L[K] Y) (x : X) (y : Y) :
    g67mBil A B (pair x y) = pure (A x) (B y) := rfl

noncomputable def g67mR (A : X →L[K] X) (B : Y →L[K] Y) : Projective K X Y →L[K] Projective K X Y :=
  extendBilinear (g67mBil A B)

theorem g67m_R_pure (A : X →L[K] X) (B : Y →L[K] Y) (x : X) (y : Y) :
    g67mR A B (pure x y) = pure (A x) (B y) := by
  rw [g67mR, g66r_ext_pure, g67m_bil_apply]

theorem g67m_R_norm (A : X →L[K] X) (B : Y →L[K] Y) : ‖g67mR A B‖ ≤ ‖A‖ * ‖B‖ :=
  (g66r_ext_norm _).trans (MultilinearMap.mkContinuous_norm_le _ (by positivity) _)

theorem g67m_R_idem (A : X →L[K] X) (B : Y →L[K] Y) (hA : A.comp A = A) (hB : B.comp B = B) :
    (g67mR A B).comp (g67mR A B) = g67mR A B := by
  apply g66r_uniq
  intro x y
  rw [ContinuousLinearMap.comp_apply, g67m_R_pure, g67m_R_pure]
  have h1 : A (A x) = A x := by simpa using congrArg (fun T : X →L[K] X => T x) hA
  have h2 : B (B y) = B y := by simpa using congrArg (fun T : Y →L[K] Y => T y) hB
  rw [h1, h2]

theorem g67m_R_fd (A : X →L[K] X) (B : Y →L[K] Y) (hA : FiniteDimensional K A.range)
    (hB : FiniteDimensional K B.range) : FiniteDimensional K (g67mR A B).range := by
  let β : LinearMap.range (A : X →ₗ[K] X) →ₗ[K] LinearMap.range (B : Y →ₗ[K] Y) →ₗ[K] Projective K X Y :=
    LinearMap.mk₂ K (fun a b => pure (a : X) (b : Y))
      (fun a a' b => by simp only [Submodule.coe_add, g67m_pure_add])
      (fun c a b => by simp only [Submodule.coe_smul, g67m_pure_smul])
      (fun a b b' => by simp only [Submodule.coe_add, g67m_pure_add'])
      (fun c a b => by simp only [Submodule.coe_smul, g67m_pure_smul'])
  let V := LinearMap.range (TensorProduct.lift β)
  haveI : FiniteDimensional K V := LinearMap.finiteDimensional_range _
  have hpure : ∀ x y, pure (K := K) (A x) (B y) ∈ V := by
    intro x y
    exact ⟨(⟨A x, LinearMap.mem_range_self _ x⟩ : LinearMap.range (A : X →ₗ[K] X)) ⊗ₜ
      (⟨B y, LinearMap.mem_range_self _ y⟩ : LinearMap.range (B : Y →ₗ[K] Y)), by
        rw [TensorProduct.lift.tmul]; rfl⟩
  have hV : IsClosed (V : Set (Projective K X Y)) := Submodule.closed_of_finiteDimensional _
  have halg : ∀ u : Algebraic K X Y, g67mR A B (algebraicInclusion u) ∈ V := by
    intro u
    induction u using PiTensorProduct.induction_on with
    | smul_tprod c m =>
      rw [map_smul, map_smul]
      refine V.smul_mem c ?_
      have : pair (m false).down (m true).down = m := by funext b; cases b <;> rfl
      rw [← this]
      show g67mR A B (pure _ _) ∈ V
      rw [g67m_R_pure]; exact hpure _ _
    | add a b ha hb =>
      rw [map_add, map_add]; exact V.add_mem ha hb
  have hle : (g67mR A B).range ≤ V := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ closure (Set.range (algebraicInclusion (K := K) (X := X) (Y := Y))) := g66r_dense z
    have := map_mem_closure (g67mR A B).continuous hz (t := (V : Set (Projective K X Y)))
      (by rintro _ ⟨u, rfl⟩; exact halg u)
    rwa [hV.closure_eq] at this
  exact Submodule.finiteDimensional_of_le hle

theorem g67m_lemA {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] (h : MetricPi K E) (t : Finset E)
    (δ : ℝ) (hδ : 0 < δ) : ∃ P : E →L[K] E, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ∀ x ∈ t, ‖x - P x‖ ≤ 2 * δ * ‖x‖ := by
  classical
  let t' := (t.filter (· ≠ 0)).image (fun x => ((‖x‖ : K))⁻¹ • x)
  have hunit : ∀ x : E, x ≠ 0 → ‖((‖x‖ : K))⁻¹ • x‖ = 1 := by
    intro x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne']
  obtain ⟨P, h1, h2, h3, h4⟩ := h δ hδ t' (by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    exact hunit x' (Finset.mem_filter.1 hx').2)
  refine ⟨P, h1, h2, h3, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set u := ((‖x‖ : K))⁻¹ • x with hu
  have hut : u ∈ t' := Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, hx0⟩, rfl⟩
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := h4 u hut
  have hPy : P (P w) = P w := by
    have := congrArg (fun T : E →L[K] E => T w) h1
    simpa using this
  have hy' : ‖u - P w‖ < δ := hy
  have hb : ‖u - P u‖ ≤ 2 * δ := by
    have e : u - P u = (u - P w) - P (u - P w) := by rw [map_sub, hPy]; abel
    rw [e]
    calc ‖(u - P w) - P (u - P w)‖ ≤ ‖u - P w‖ + ‖P (u - P w)‖ := norm_sub_le _ _
      _ ≤ ‖u - P w‖ + ‖u - P w‖ := by
          gcongr
          exact (P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h2)
      _ ≤ 2 * δ := by linarith
  have hxu : x = ((‖x‖ : K)) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxp.ne'), one_smul]
  rw [hxu, map_smul, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos hxp]
  rw [← hxu]
  nlinarith

theorem solution [CompleteSpace X] [CompleteSpace Y] (hX : MetricPi K X) (hY : MetricPi K Y) :
    MetricPi K (Projective K X Y) := by
  classical
  intro ε hε s hs
  have hrep : ∀ z : Projective K X Y, ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
      ‖z - ∑ i, pure (K := K) (x i) (y i)‖ < ε / 3 := by
    intro z
    obtain ⟨u, hu⟩ := Metric.denseRange_iff.1 (g66r_dense (K := K) (X := X) (Y := Y)) z (ε / 3) (by linarith)
    obtain ⟨⟨r, n, x, y, hu', -⟩, -, -⟩ := g66s_cost u
    refine ⟨n, x, y, ?_⟩
    rw [← dist_eq_norm]
    convert hu using 2
    rw [hu', map_sum]; rfl
  choose n xs ys hxy using hrep
  set M : ℝ := ∑ z ∈ s, ∑ i, ‖xs z i‖ * ‖ys z i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  set δ : ℝ := ε / (6 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ := g67m_lemA (K := K) hX (s.biUnion fun z => Finset.univ.image (xs z)) δ hδ0
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := g67m_lemA (K := K) hY (s.biUnion fun z => Finset.univ.image (ys z)) δ hδ0
  refine ⟨g67mR A B, g67m_R_idem A B hA1 hB1, (g67m_R_norm A B).trans ?_, g67m_R_fd A B hA3 hB3,
    fun z hz => ⟨g67mR A B (∑ i, pure (K := K) (xs z i) (ys z i)), ⟨_, rfl⟩, ?_⟩⟩
  · calc ‖A‖ * ‖B‖ ≤ 1 * 1 := mul_le_mul hA2 hB2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hxA : ∀ i, ‖xs z i - A (xs z i)‖ ≤ 2 * δ * ‖xs z i‖ := fun i =>
    hA4 _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hyB : ∀ i, ‖ys z i - B (ys z i)‖ ≤ 2 * δ * ‖ys z i‖ := fun i =>
    hB4 _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hAx : ∀ i, ‖A (xs z i)‖ ≤ ‖xs z i‖ := fun i =>
    (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA2)
  have hterm : ∀ i, ‖pure (K := K) (xs z i) (ys z i) - g67mR A B (pure (xs z i) (ys z i))‖ ≤
      4 * δ * (‖xs z i‖ * ‖ys z i‖) := by
    intro i
    rw [g67m_R_pure]
    have e : pure (K := K) (xs z i) (ys z i) - pure (A (xs z i)) (B (ys z i)) =
        pure (xs z i - A (xs z i)) (ys z i) + pure (A (xs z i)) (ys z i - B (ys z i)) := by
      rw [g67m_pure_sub, g67m_pure_sub']; abel
    rw [e]
    calc _ ≤ ‖pure (K := K) (xs z i - A (xs z i)) (ys z i)‖ + ‖pure (K := K) (A (xs z i)) (ys z i - B (ys z i))‖ :=
          norm_add_le _ _
      _ ≤ (2 * δ * ‖xs z i‖) * ‖ys z i‖ + ‖xs z i‖ * (2 * δ * ‖ys z i‖) := by
          rw [g66s_cross, g66s_cross]
          gcongr
          · exact hxA i
          · exact hAx i
          · exact hyB i
      _ = 4 * δ * (‖xs z i‖ * ‖ys z i‖) := by ring
  have hzM : ∑ i, ‖xs z i‖ * ‖ys z i‖ ≤ M :=
    Finset.single_le_sum (f := fun z => ∑ i, ‖xs z i‖ * ‖ys z i‖)
      (fun z _ => Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hz
  have hw : ‖∑ i, pure (K := K) (xs z i) (ys z i) - g67mR A B (∑ i, pure (K := K) (xs z i) (ys z i))‖
      ≤ 4 * δ * M := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hzM (by positivity)
  have h4 : 4 * δ * M < 2 * ε / 3 := by
    rw [hδ]
    rw [show 4 * (ε / (6 * (M + 1))) * M = (2 * ε / 3) * (M / (M + 1)) by field_simp; ring]
    have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have h2 : 0 < 2 * ε / 3 := by positivity
    nlinarith
  calc ‖z - g67mR A B (∑ i, pure (K := K) (xs z i) (ys z i))‖
      ≤ ‖z - ∑ i, pure (K := K) (xs z i) (ys z i)‖ +
        ‖∑ i, pure (K := K) (xs z i) (ys z i) - g67mR A B (∑ i, pure (K := K) (xs z i) (ys z i))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 3 + 2 * ε / 3 := add_lt_add_of_lt_of_le (hxy z) (hw.trans h4.le)
    _ = ε := by ring

end Banach


end
