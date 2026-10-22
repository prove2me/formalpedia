-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.bilinear_attainment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:12:33.401729+00:00
-- url     : https://prove2.me/submissions/0f009dee-3c3e-494c-be95-dfb6ca437f29

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

theorem g67_pair_smul (B : Bilinear K X Y K) (c d : K) (x : X) (y : Y) :
    B (pair (c • x) (d • y)) = c * d * B (pair x y) := by
  have e1 : pair (c • x) (d • y) =
      Function.update (pair x (d • y)) false (c • pair x (d • y) false) := by
    funext b; cases b <;> rfl
  have e2 : pair x (d • y) =
      Function.update (pair x y) true (d • pair x y true) := by
    funext b; cases b <;> rfl
  rw [e1, B.map_update_smul, Function.update_eq_self, e2, B.map_update_smul, Function.update_eq_self,
    smul_eq_mul, smul_eq_mul, mul_assoc]

theorem solution [CompleteSpace X] [CompleteSpace Y] (B : Bilinear K X Y K) (z : Projective K X Y)
    (hz : ‖z‖ = 1) (ha : TensorAttains z) (hB : ‖extendBilinear B z‖ = ‖B‖) :
    BilinearAttains B := by
  obtain ⟨x, y, ⟨⟨C, hC⟩, hsum, hzs⟩, hcost⟩ := ha
  have hev : HasSum (fun n => B (pair (x n) (y n))) (extendBilinear B z) := by
    have := (extendBilinear B).hasSum hzs
    simpa [g66r_ext_pure] using this
  have hle : ∀ n, ‖B (pair (x n) (y n))‖ ≤ ‖B‖ * (‖x n‖ * ‖y n‖) := by
    intro n
    have := B.le_opNorm (pair (x n) (y n))
    rwa [g66s_pair_norm] at this
  have hs1 : Summable fun n => ‖B (pair (x n) (y n))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle (hsum.mul_left _)
  have hdiff : HasSum (fun n => ‖B‖ * (‖x n‖ * ‖y n‖) - ‖B (pair (x n) (y n))‖)
      (‖B‖ * 1 - ∑' n, ‖B (pair (x n) (y n))‖) := by
    have h := (hsum.mul_left ‖B‖).hasSum.sub hs1.hasSum
    rw [tsum_mul_left, ← hcost, hz] at h
    exact h
  have hnn : ∀ n, 0 ≤ ‖B‖ * (‖x n‖ * ‖y n‖) - ‖B (pair (x n) (y n))‖ := fun n => sub_nonneg.2 (hle n)
  have hsum_le : ‖B‖ ≤ ∑' n, ‖B (pair (x n) (y n))‖ := by
    rw [← hB, ← hev.tsum_eq]; exact norm_tsum_le_tsum_norm hs1
  have htot : ‖B‖ * 1 - ∑' n, ‖B (pair (x n) (y n))‖ = 0 := by
    have := hasSum_le (fun n => hnn n) hasSum_zero hdiff
    linarith
  rw [htot] at hdiff
  have hzero := (hasSum_zero_iff_of_nonneg hnn).1 hdiff
  -- some term is nonzero
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  obtain ⟨n, hn⟩ : ∃ n, ‖x n‖ * ‖y n‖ ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [tsum_congr hc, tsum_zero, hz] at hcost
    exact one_ne_zero hcost
  have hxn : x n ≠ 0 := fun h => hn (by rw [h, norm_zero, zero_mul])
  have hyn : y n ≠ 0 := fun h => hn (by rw [h, norm_zero, mul_zero])
  have hx0 : 0 < ‖x n‖ := norm_pos_iff.2 hxn
  have hy0 : 0 < ‖y n‖ := norm_pos_iff.2 hyn
  have heq : ‖B (pair (x n) (y n))‖ = ‖B‖ * (‖x n‖ * ‖y n‖) := by
    have := congrFun hzero n; simp only [Pi.zero_apply] at this; linarith
  refine ⟨((‖x n‖ : K))⁻¹ • x n, ((‖y n‖ : K))⁻¹ • y n, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne']
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hy0, inv_mul_cancel₀ hy0.ne']
  · rw [g67_pair_smul, norm_mul, norm_mul, norm_inv, norm_inv, RCLike.norm_ofReal, RCLike.norm_ofReal,
      abs_of_pos hx0, abs_of_pos hy0, heq]
    field_simp

end Banach


end
