-- Prove2me | solution 1 for PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b7bea088-eff3-5c4a-b1d0-48ab5ff64e42

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq

set_option autoImplicit false

noncomputable section

namespace TP10

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section cocycle

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p))

def IsCoc (c : F.fixingSubgroup → ℂ_[p]) : Prop :=
  ∀ σ τ : F.fixingSubgroup, c (σ * τ) = c σ + (σ : Γ) • c τ

def cob (b : ℂ_[p]) : F.fixingSubgroup → ℂ_[p] := fun σ => (σ : Γ) • b - b

variable {F}

lemma isCoc_cob (b : ℂ_[p]) : IsCoc F (cob F b) := by
  intro σ τ
  simp only [cob, Subgroup.coe_mul, mul_smul, smul_sub]
  abel

lemma IsCoc.sub {c c' : F.fixingSubgroup → ℂ_[p]} (hc : IsCoc F c) (hc' : IsCoc F c') :
    IsCoc F (c - c') := by
  intro σ τ
  simp only [Pi.sub_apply, hc σ τ, hc' σ τ, smul_sub]
  abel

lemma IsCoc.map_one {c : F.fixingSubgroup → ℂ_[p]} (hc : IsCoc F c) : c 1 = 0 := by
  have := hc 1 1
  rw [mul_one, Subgroup.coe_one, one_smul] at this
  linear_combination -this

lemma IsCoc.apply_mul_sub {c : F.fixingSubgroup → ℂ_[p]} (hc : IsCoc F c) (σ u : F.fixingSubgroup) :
    c (σ * u) - c σ = (σ : Γ) • c u := by
  rw [hc]; abel

lemma cob_add (b b' : ℂ_[p]) : cob F (b + b') = cob F b + cob F b' := by
  funext σ; simp only [cob, Pi.add_apply, smul_add]; abel

lemma cob_zero : cob F (0 : ℂ_[p]) = 0 := by
  funext σ; simp [cob]

lemma cob_sum {ι : Type*} (s : Finset ι) (b : ι → ℂ_[p]) :
    cob F (∑ i ∈ s, b i) = ∑ i ∈ s, cob F (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cob_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cob_add, ih]

lemma continuous_orbit (b : ℂ_[p]) : Continuous fun σ : Γ => σ • b := by
  refine continuous_iff_continuousAt.2 fun σ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := Ω)) b ε hε
  let E : IntermediateField ℚ_[p] Ω := IntermediateField.adjoin ℚ_[p] {a}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hU : IsOpen (E.fixingSubgroup : Set Γ) := IntermediateField.fixingSubgroup_isOpen E
  have hV : IsOpen {x : Γ | σ⁻¹ * x ∈ E.fixingSubgroup} :=
    hU.preimage (continuous_const_mul σ⁻¹)
  have hσV : σ ∈ {x : Γ | σ⁻¹ * x ∈ E.fixingSubgroup} := by
    show σ⁻¹ * σ ∈ E.fixingSubgroup; rw [inv_mul_cancel]; exact Subgroup.one_mem _
  filter_upwards [hV.mem_nhds hσV] with x hx
  set u := σ⁻¹ * x with hu
  have hxu : x = σ * u := by rw [hu, mul_inv_cancel_left]
  have hua : u • ((a : Ω) : ℂ_[p]) = (a : ℂ_[p]) := by
    rw [PadicComplex.smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hx a
      (IntermediateField.mem_adjoin_simple_self ℚ_[p] a)]
  rw [dist_eq_norm, hxu, mul_smul, ← smul_sub, PadicComplex.norm_smul_eq]
  have : u • b - b = u • (b - a) - (b - a) := by rw [smul_sub, hua]; abel
  rw [this]
  calc ‖u • (b - ↑a) - (b - ↑a)‖ ≤ max ‖u • (b - ↑a)‖ ‖-(b - ↑a)‖ := by
        rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
    _ = ‖b - ↑a‖ := by rw [norm_neg, PadicComplex.norm_smul_eq, max_self]
    _ < ε := by rwa [← dist_eq_norm]

lemma continuous_cob (b : ℂ_[p]) : Continuous (cob F b) := by
  unfold cob
  exact ((continuous_orbit b).comp continuous_subtype_val).sub continuous_const

variable (F) in

scoped instance compactSpace_fixingSubgroup : CompactSpace F.fixingSubgroup :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed F).isCompact

lemma exists_bound {c : F.fixingSubgroup → ℂ_[p]} (hc : Continuous c) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ, ‖c σ‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := F.fixingSubgroup)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨max C 1, lt_max_of_lt_right one_pos, fun σ => (hC σ (Set.mem_univ _)).trans (le_max_left _ _)⟩

lemma exists_level {c : F.fixingSubgroup → ℂ_[p]} (hc : IsCoc F c) (hcont : Continuous c)
    {η : ℝ} (hη : 0 < η) :
    ∃ M₁ : IntermediateField ℚ_[p] Ω, FiniteDimensional ℚ_[p] M₁ ∧
      ∀ σ : F.fixingSubgroup, (σ : Γ) ∈ M₁.fixingSubgroup → ‖c σ‖ ≤ η := by
  let S : Set F.fixingSubgroup := {σ | ‖c σ‖ < η}
  have hS : IsOpen S := isOpen_lt (continuous_norm.comp hcont) continuous_const
  have h1 : (1 : F.fixingSubgroup) ∈ S := by
    show ‖c 1‖ < η
    rw [hc.map_one, norm_zero]; exact hη
  obtain ⟨u, hu, huS⟩ := (mem_nhds_subtype _ _ _).1 (hS.mem_nhds h1)
  rw [Subgroup.coe_one] at hu
  obtain ⟨M₁, hM₁, hM₁u⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] Ω u).1 hu
  refine ⟨M₁, hM₁, fun σ hσ => le_of_lt ?_⟩
  exact huS (hM₁u hσ)

end cocycle

section level

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (M₁ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M₁]

def USub : Subgroup F.fixingSubgroup := M₁.fixingSubgroup.subgroupOf F.fixingSubgroup

omit [FiniteDimensional ℚ_[p] M₁] in
lemma mem_USub {σ : F.fixingSubgroup} : σ ∈ USub F M₁ ↔ (σ : Γ) ∈ M₁.fixingSubgroup :=
  Subgroup.mem_subgroupOf

def bM : Module.Basis (Fin (Module.finrank ℚ_[p] M₁)) ℚ_[p] M₁ := Module.finBasis ℚ_[p] M₁

def gens : Set Ω := Set.range fun i => ((bM M₁ i : M₁) : Ω)

def LF : IntermediateField F Ω := IntermediateField.adjoin F (gens M₁)

scoped instance LF_finiteDimensional : FiniteDimensional F (LF F M₁) := by
  haveI : Finite (gens M₁) := Set.finite_range _ |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x).tower_top

lemma bM_mem_LF (i : Fin (Module.finrank ℚ_[p] M₁)) : ((bM M₁ i : M₁) : Ω) ∈ LF F M₁ :=
  IntermediateField.subset_adjoin F _ ⟨i, rfl⟩

variable {F M₁}

lemma apply_eq_of_mem_USub {σ : F.fixingSubgroup} (hσ : σ ∈ USub F M₁) {x : Ω} (hx : x ∈ LF F M₁) :
    (σ : Γ) x = x := by
  rw [mem_USub] at hσ
  change x ∈ IntermediateField.adjoin F (gens M₁) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (bM M₁ i).2
  | algebraMap x => exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ x.2
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

lemma mem_USub_of_forall {σ : F.fixingSubgroup} (h : ∀ i, (σ : Γ) ((bM M₁ i : M₁) : Ω) = bM M₁ i) :
    σ ∈ USub F M₁ := by
  rw [mem_USub, IntermediateField.mem_fixingSubgroup_iff]
  intro m hm
  have hrepr : (⟨m, hm⟩ : M₁) = ∑ i, (bM M₁).repr ⟨m, hm⟩ i • bM M₁ i := ((bM M₁).sum_repr _).symm
  have hm' : m = ∑ i, (bM M₁).repr ⟨m, hm⟩ i • ((bM M₁ i : M₁) : Ω) := by
    have := congrArg (M₁.val) hrepr
    rw [map_sum] at this
    simp only [IntermediateField.val_mk, map_smul, IntermediateField.coe_val] at this
    exact this
  rw [hm', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, h i]

def res (σ : F.fixingSubgroup) : LF F M₁ →ₐ[F] Ω :=
  ((IntermediateField.fixingSubgroupEquiv F σ : Ω ≃ₐ[F] Ω) : Ω →ₐ[F] Ω).comp (LF F M₁).val

@[scoped simp] lemma res_apply (σ : F.fixingSubgroup) (x : LF F M₁) : res σ x = (σ : Γ) (x : Ω) := rfl

lemma res_eq_res_iff (σ τ : F.fixingSubgroup) :
    res (M₁ := M₁) σ = res τ ↔ (QuotientGroup.mk σ : F.fixingSubgroup ⧸ USub F M₁) = QuotientGroup.mk τ := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    apply mem_USub_of_forall
    intro i
    have := congrArg (fun φ => φ ⟨_, bM_mem_LF F M₁ i⟩) h
    simp only [res_apply] at this
    show ((σ : Γ)⁻¹ * (τ : Γ)) _ = _
    rw [AlgEquiv.mul_apply, ← this, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  · intro h
    ext x
    simp only [res_apply]
    have hfix := apply_eq_of_mem_USub h x.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply] at hfix
    calc (σ : Γ) (x : Ω) = (σ : Γ) ((σ : Γ)⁻¹ ((τ : Γ) (x : Ω))) := by rw [hfix]
      _ = (τ : Γ) (x : Ω) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

lemma res_surjective : Function.Surjective (res (F := F) (M₁ := M₁)) := by
  intro φ
  let ψ : Ω →ₐ[F] Ω := φ.liftNormal Ω
  let g : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective ψ (AlgHom.normal_bijective F Ω Ω ψ)
  refine ⟨(IntermediateField.fixingSubgroupEquiv F).symm g, ?_⟩
  ext x
  rw [res_apply]
  change g (x : Ω) = φ x
  have h := φ.liftNormal_commutes Ω x
  rw [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

def resQ (q : F.fixingSubgroup ⧸ USub F M₁) : LF F M₁ →ₐ[F] Ω := res q.out

lemma resQ_bijective : Function.Bijective (resQ (F := F) (M₁ := M₁)) := by
  constructor
  · intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (res_eq_res_iff _ _).1 h
  · intro φ
    obtain ⟨σ, rfl⟩ := res_surjective φ
    refine ⟨QuotientGroup.mk σ, ?_⟩
    show res (QuotientGroup.mk σ : F.fixingSubgroup ⧸ USub F M₁).out = res σ
    rw [res_eq_res_iff, QuotientGroup.out_eq']

scoped instance finite_quot : Finite (F.fixingSubgroup ⧸ USub F M₁) :=
  Finite.of_injective _ (resQ_bijective (F := F) (M₁ := M₁)).1

scoped instance fintype_quot : Fintype (F.fixingSubgroup ⧸ USub F M₁) := Fintype.ofFinite _

lemma sum_quot_apply_eq_trace (y : LF F M₁) :
    ∑ q : F.fixingSubgroup ⧸ USub F M₁, ((q.out : F.fixingSubgroup) : Γ) (y : Ω) =
      algebraMap F Ω (Algebra.trace F (LF F M₁) y) := by
  rw [trace_eq_sum_embeddings Ω]
  exact Fintype.sum_bijective _ resQ_bijective _ _ fun q => rfl

end level

section step

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p))

def AE : Prop :=
  ∀ (L : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F L] (x : F),
    ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F L y = x

variable {F}

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
lemma p_pos : (0 : ℝ) < p := lt_trans one_pos one_lt_p

lemma natCast_p_eq : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by
  rw [map_natCast]

lemma norm_natCast_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [natCast_p_eq, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  rw [show (algebraMap (PadicAlgCl p) ℂ_[p]) (algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])) =
      ((algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) from rfl,
    PadicComplex.norm_extends', Padic.norm_p]

lemma natCast_p_ne_zero : ((p : ℕ) : ℂ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma norm_inv_natCast_p : ‖((p : ℕ) : ℂ_[p])⁻¹‖ = (p : ℝ) := by
  rw [norm_inv, norm_natCast_p, inv_inv]

lemma smul_inv_natCast_p (σ : Γ) : σ • ((p : ℕ) : ℂ_[p])⁻¹ = ((p : ℕ) : ℂ_[p])⁻¹ := by
  rw [smul_inv'', natCast_p_eq, PadicComplex.smul_algebraMap]

lemma norm_coe_p_lt_one : ‖((algebraMap ℚ_[p] F (p : ℚ_[p]) : F) : PadicAlgCl p)‖ < 1 := by
  rw [show ((algebraMap ℚ_[p] F (p : ℚ_[p]) : F) : PadicAlgCl p) =
      algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) from rfl]
  rw [show algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) = ((p : ℚ_[p]) : PadicAlgCl p) from rfl,
    PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ one_lt_p

theorem step (hF : AE F) {f : F.fixingSubgroup → ℂ_[p]} (hf : IsCoc F f) (hfc : Continuous f)
    {M : ℝ} (hM : 0 < M) (hb : ∀ σ, ‖f σ‖ ≤ M) :
    ∃ g : ℂ_[p], ‖g‖ ≤ p * M ∧ ∀ σ, ‖f σ - cob F g σ‖ ≤ M / p := by
  classical
  have hp0 := p_pos (p := p)
  set η : ℝ := M / (p : ℝ) ^ 2 with hη
  have hη0 : 0 < η := by positivity

  obtain ⟨M₁, hM₁fd, hM₁⟩ := exists_level hf hfc hη0
  haveI := hM₁fd
  have hU : ∀ u : F.fixingSubgroup, u ∈ USub F M₁ → ‖f u‖ ≤ η := fun u hu =>
    hM₁ u ((mem_USub F M₁).1 hu)

  obtain ⟨yL, hyL1, hyLtr⟩ := hF (LF F M₁) (algebraMap ℚ_[p] F (p : ℚ_[p])) norm_coe_p_lt_one
  set y : ℂ_[p] := ((yL : Ω) : ℂ_[p]) with hy
  have hy1 : ‖y‖ ≤ 1 := by rw [hy, PadicComplex.norm_extends]; exact hyL1
  have hyU : ∀ u : F.fixingSubgroup, u ∈ USub F M₁ → (u : Γ) • y = y := by
    intro u hu
    rw [hy, PadicComplex.smul_coe, apply_eq_of_mem_USub hu yL.2]

  set Q := F.fixingSubgroup ⧸ USub F M₁
  let Y : Q → ℂ_[p] := fun q => ((q.out : F.fixingSubgroup) : Γ) • y
  have hYnorm : ∀ q, ‖Y q‖ ≤ 1 := fun q => by
    show ‖((q.out : F.fixingSubgroup) : Γ) • y‖ ≤ 1
    rw [PadicComplex.norm_smul_eq]; exact hy1

  have hYsum : ∑ q : Q, Y q = ((p : ℕ) : ℂ_[p]) := by
    have h1 : ∀ q : Q, Y q = (UniformSpace.Completion.coeRingHom : Ω →+* ℂ_[p])
        (((q.out : F.fixingSubgroup) : Γ) (yL : Ω)) := fun q => by
      show ((q.out : F.fixingSubgroup) : Γ) • y = _
      rw [hy, PadicComplex.smul_coe]; rfl
    simp_rw [h1]
    rw [← map_sum, sum_quot_apply_eq_trace, hyLtr]
    change (((algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])) : Ω) : ℂ_[p]) = _
    rw [map_natCast, PadicComplex.coe_natCast]

  have hYact : ∀ (τ : F.fixingSubgroup) (q : Q), Y (τ • q) = (τ : Γ) • Y q := by
    intro τ q
    have h1 : (τ • q : Q) = QuotientGroup.mk (τ * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (USub F M₁) (τ * q.out)
    show (((τ • q : Q).out : F.fixingSubgroup) : Γ) • y = (τ : Γ) • ((q.out : F.fixingSubgroup) : Γ) • y
    rw [h1, hu, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, hyU _ u.2]

  have hE : ∀ (τ : F.fixingSubgroup) (q : Q),
      ‖f (τ • q).out - f τ - (τ : Γ) • f q.out‖ ≤ η := by
    intro τ q
    have h1 : (τ • q : Q) = QuotientGroup.mk (τ * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (USub F M₁) (τ * q.out)
    rw [h1, hu, hf (τ * q.out) u, hf τ q.out]
    have : f τ + (τ : Γ) • f q.out + ((τ * q.out : F.fixingSubgroup) : Γ) • f u - f τ -
        (τ : Γ) • f q.out = ((τ * q.out : F.fixingSubgroup) : Γ) • f u := by abel
    rw [this, PadicComplex.norm_smul_eq]
    exact hU _ u.2

  set S : ℂ_[p] := ∑ q : Q, Y q * f q.out with hS
  set g : ℂ_[p] := -(((p : ℕ) : ℂ_[p])⁻¹ * S) with hg
  refine ⟨g, ?_, ?_⟩
  ·
    rw [hg, norm_neg, norm_mul, norm_inv_natCast_p]
    refine mul_le_mul_of_nonneg_left ?_ hp0.le
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM.le fun q _ => ?_
    rw [norm_mul]
    calc ‖Y q‖ * ‖f q.out‖ ≤ 1 * M :=
          mul_le_mul (hYnorm q) (hb _) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  · intro τ

    have hre1 : ∑ q : Q, Y (τ • q) * f (τ • q).out = S :=
      Equiv.sum_comp (MulAction.toPerm (τ : F.fixingSubgroup)) (fun q : Q => Y q * f q.out)
    have hre2 : ∑ q : Q, Y (τ • q) = ((p : ℕ) : ℂ_[p]) := by
      rw [← hYsum]
      exact Equiv.sum_comp (MulAction.toPerm (τ : F.fixingSubgroup)) Y

    set D : Q → ℂ_[p] := fun q => Y (τ • q) * (f (τ • q).out - f τ - (τ : Γ) • f q.out) with hD
    have hτS : (τ : Γ) • S = S - ((p : ℕ) : ℂ_[p]) * f τ - ∑ q : Q, D q := by
      rw [hS, Finset.smul_sum]
      have : ∀ q : Q, (τ : Γ) • (Y q * f q.out) =
          Y (τ • q) * f (τ • q).out - Y (τ • q) * f τ - D q := by
        intro q
        rw [smul_mul', ← hYact, hD]
        ring
      simp_rw [this]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hre1, ← Finset.sum_mul, hre2]
    have hDnorm : ‖∑ q : Q, D q‖ ≤ η := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hη0.le fun q _ => ?_
      rw [hD, norm_mul]
      calc ‖Y (τ • q)‖ * ‖f (τ • q).out - f τ - (τ : Γ) • f q.out‖ ≤ 1 * η :=
            mul_le_mul (hYnorm _) (hE τ q) (norm_nonneg _) zero_le_one
        _ = η := one_mul η
    have hkey : f τ - cob F g τ = -(((p : ℕ) : ℂ_[p])⁻¹ * ∑ q : Q, D q) := by
      simp only [cob, hg, smul_neg, smul_mul', smul_inv_natCast_p, hτS]
      field_simp [natCast_p_ne_zero (p := p)]
      ring
    rw [hkey, norm_neg, norm_mul, norm_inv_natCast_p]
    calc (p : ℝ) * ‖∑ q : Q, D q‖ ≤ p * η := mul_le_mul_of_nonneg_left hDnorm hp0.le
      _ = M / p := by rw [hη]; field_simp

end step

section iterate

variable {F : IntermediateField ℚ_[p] (PadicAlgCl p)} (hF : AE F)
include hF

open Classical in

def corr (f : F.fixingSubgroup → ℂ_[p]) (M : ℝ) : ℂ_[p] :=
  if h : IsCoc F f ∧ Continuous f ∧ 0 < M ∧ ∀ σ, ‖f σ‖ ≤ M then
    Classical.choose (step hF h.1 h.2.1 h.2.2.1 h.2.2.2) else 0

lemma corr_spec {f : F.fixingSubgroup → ℂ_[p]} {M : ℝ} (h1 : IsCoc F f) (h2 : Continuous f)
    (h3 : 0 < M) (h4 : ∀ σ, ‖f σ‖ ≤ M) :
    ‖corr hF f M‖ ≤ p * M ∧ ∀ σ, ‖f σ - cob F (corr hF f M) σ‖ ≤ M / p := by
  have h : IsCoc F f ∧ Continuous f ∧ 0 < M ∧ ∀ σ, ‖f σ‖ ≤ M := ⟨h1, h2, h3, h4⟩
  rw [corr, dif_pos h]
  exact Classical.choose_spec (step hF h.1 h.2.1 h.2.2.1 h.2.2.2)

variable (f₀ : F.fixingSubgroup → ℂ_[p]) (M₀ : ℝ)

def seq : ℕ → (F.fixingSubgroup → ℂ_[p])
  | 0 => f₀
  | k + 1 => seq k - cob F (corr hF (seq k) (M₀ / (p : ℝ) ^ k))

def term (k : ℕ) : ℂ_[p] := corr hF (seq hF f₀ M₀ k) (M₀ / (p : ℝ) ^ k)

lemma seq_succ (k : ℕ) : seq hF f₀ M₀ (k + 1) = seq hF f₀ M₀ k - cob F (term hF f₀ M₀ k) := rfl

variable {f₀ M₀}
variable (h₀ : IsCoc F f₀) (hc₀ : Continuous f₀) (hM₀ : 0 < M₀) (hb₀ : ∀ σ, ‖f₀ σ‖ ≤ M₀)
include h₀ hc₀ hM₀ hb₀

lemma seq_spec (k : ℕ) : IsCoc F (seq hF f₀ M₀ k) ∧ Continuous (seq hF f₀ M₀ k) ∧
    ∀ σ, ‖seq hF f₀ M₀ k σ‖ ≤ M₀ / (p : ℝ) ^ k := by
  induction k with
  | zero => exact ⟨h₀, hc₀, by simp at hb₀ ⊢; exact hb₀⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hMk : 0 < M₀ / (p : ℝ) ^ k := div_pos hM₀ (pow_pos p_pos k)
    have hs := corr_spec hF h1 h2 hMk h3
    refine ⟨h1.sub (isCoc_cob _), h2.sub (continuous_cob _), fun σ => ?_⟩
    rw [seq_succ, Pi.sub_apply]
    calc ‖seq hF f₀ M₀ k σ - cob F (term hF f₀ M₀ k) σ‖ ≤ M₀ / (p : ℝ) ^ k / p := hs.2 σ
      _ = M₀ / (p : ℝ) ^ (k + 1) := by rw [pow_succ, div_div]

lemma norm_term_le (k : ℕ) : ‖term hF f₀ M₀ k‖ ≤ p * M₀ * ((p : ℝ)⁻¹) ^ k := by
  obtain ⟨h1, h2, h3⟩ := seq_spec hF h₀ hc₀ hM₀ hb₀ k
  have hMk : 0 < M₀ / (p : ℝ) ^ k := div_pos hM₀ (pow_pos p_pos k)
  calc ‖term hF f₀ M₀ k‖ ≤ p * (M₀ / (p : ℝ) ^ k) := (corr_spec hF h1 h2 hMk h3).1
    _ = p * M₀ * ((p : ℝ)⁻¹) ^ k := by rw [inv_pow, div_eq_mul_inv, mul_assoc]

omit h₀ hc₀ hM₀ hb₀ in
lemma seq_eq_sub (k : ℕ) :
    seq hF f₀ M₀ k = f₀ - cob F (∑ j ∈ Finset.range k, term hF f₀ M₀ j) := by
  induction k with
  | zero => simp [seq, cob_zero]
  | succ k ih =>
    rw [seq_succ, ih, Finset.sum_range_succ, cob_add]
    abel

theorem exists_eq_cob : ∃ b : ℂ_[p], ∀ σ, f₀ σ = cob F b σ := by
  have hp1 := one_lt_p (p := p)
  have hp0 := p_pos (p := p)
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.2 hp0.le
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1

  have hsum : Summable (term hF f₀ M₀) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left (p * M₀))
      (norm_term_le hF h₀ hc₀ hM₀ hb₀)
  set b : ℂ_[p] := ∑' j, term hF f₀ M₀ j
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, term hF f₀ M₀ j) atTop (𝓝 b) :=
    hsum.hasSum.tendsto_sum_nat
  refine ⟨b, fun σ => ?_⟩

  have hcobc : Continuous fun z : ℂ_[p] => cob F z σ :=
    (continuous_const_smul _).sub continuous_id
  have hlim1 : Tendsto (fun k => seq hF f₀ M₀ k σ) atTop (𝓝 (f₀ σ - cob F b σ)) := by
    have : (fun k => seq hF f₀ M₀ k σ) =
        fun k => f₀ σ - cob F (∑ j ∈ Finset.range k, term hF f₀ M₀ j) σ := by
      funext k; rw [seq_eq_sub]; rfl
    rw [this]
    exact tendsto_const_nhds.sub ((hcobc.tendsto b).comp hpart)

  have hlim2 : Tendsto (fun k => seq hF f₀ M₀ k σ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (seq_spec hF h₀ hc₀ hM₀ hb₀ k).2.2 σ) ?_
    have : (fun k => M₀ / (p : ℝ) ^ k) = fun k => M₀ * ((p : ℝ)⁻¹) ^ k := by
      funext k; rw [inv_pow, div_eq_mul_inv]
    rw [this, ← mul_zero M₀]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul M₀
  have := tendsto_nhds_unique hlim1 hlim2
  exact (sub_eq_zero.1 this)

end iterate

end TP10
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq.TP10"

open TP10 in
theorem solution
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hF : ∀ (L : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F L] (x : F),
      ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F L y = x)
    (c : F.fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : F.fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : F.fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b := by
  have hcoc : IsCoc F c := hcocycle
  have hAE : AE F := fun L _ x hx => hF L x hx
  obtain ⟨M₀, hM₀, hbd⟩ := exists_bound hc
  obtain ⟨b, hb⟩ := exists_eq_cob hAE hcoc hc hM₀ hbd
  exact ⟨b, hb⟩

end
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq.TP10"

end S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
end P2MW
export P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq (solution)
