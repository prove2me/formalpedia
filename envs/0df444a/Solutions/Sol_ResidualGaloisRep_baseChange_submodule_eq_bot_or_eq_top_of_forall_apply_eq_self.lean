-- Prove2me | solution 1 for ResidualGaloisRep.baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b851a0be-7317-5f76-befa-8acb7548e7d2

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self

set_option autoImplicit false

open Module TensorProduct

noncomputable section

namespace P2mCliff

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section BC

variable {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
  {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma forall_mem_of_forall_baseChange (W : Submodule K (K ⊗[k] V))
    (hW : ∀ f : Module.End k V, ∀ x ∈ W, f.baseChange K x ∈ W) :
    ∀ g : Module.End K (K ⊗[k] V), ∀ x ∈ W, g x ∈ W := by
  classical
  let b := Module.finBasis k V
  let bK := Algebra.TensorProduct.basis K b
  let P : Submodule K (Module.End K (K ⊗[k] V)) :=
    { carrier := {g | ∀ x ∈ W, g x ∈ W}
      zero_mem' := fun x _ => by simp
      add_mem' := fun hf hg x hx => by simpa using W.add_mem (hf x hx) (hg x hx)
      smul_mem' := fun c f hf x hx => by simpa using W.smul_mem c (hf x hx) }
  have hbasis : ∀ ij, (bK.linearMap bK) ij ∈ P := by
    intro ij x hx
    have := hW (b.linearMap b ij) x hx
    rwa [Module.Basis.baseChange_linearMap] at this
  have htop : (⊤ : Submodule K (Module.End K (K ⊗[k] V))) ≤ P := by
    rw [← (bK.linearMap bK).span_eq, Submodule.span_le]
    rintro _ ⟨ij, rfl⟩
    exact hbasis ij
  intro g x hx
  exact htop (Submodule.mem_top : g ∈ ⊤) x hx

lemma eq_bot_or_eq_top_of_forall_mem {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M]
    (W : Submodule L M) (hW : ∀ g : Module.End L M, ∀ x ∈ W, g x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hbot
  rw [eq_top_iff]
  rintro y -
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L M, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff L x).1 h)
  have hmem := hW ((φ x)⁻¹ • φ.smulRight y) x hxW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using hmem

lemma forall_baseChange_of_span_eq_top {S : Set (Module.End k V)}
    (hS : Submodule.span k S = ⊤) (W : Submodule K (K ⊗[k] V))
    (hW : ∀ f ∈ S, ∀ x ∈ W, f.baseChange K x ∈ W) :
    ∀ f : Module.End k V, ∀ x ∈ W, f.baseChange K x ∈ W := by
  let P : Submodule k (Module.End k V) :=
    { carrier := {f | ∀ x ∈ W, f.baseChange K x ∈ W}
      zero_mem' := fun x _ => by simp [LinearMap.baseChange_zero]
      add_mem' := fun hf hg x hx => by
        simpa [LinearMap.baseChange_add] using W.add_mem (hf x hx) (hg x hx)
      smul_mem' := fun c f hf x hx => by
        show (LinearMap.baseChange K (c • f)) x ∈ W
        rw [LinearMap.baseChange_smul, LinearMap.smul_apply, ← algebraMap_smul K c]
        exact W.smul_mem (algebraMap k K c) (hf x hx) }
  have h : (⊤ : Submodule k (Module.End k V)) ≤ P := by
    rw [← hS, Submodule.span_le]
    exact fun f hf => hW f hf
  intro f
  exact h (Submodule.mem_top : f ∈ ⊤)

lemma exists_eq_smul_one_of_baseChange_eq_smul_one [Nontrivial V] (T : Module.End k V) (c : K)
    (h : T.baseChange K = c • 1) : ∃ a : k, T = a • 1 := by
  classical
  let b := Module.finBasis k V
  let bK := Algebra.TensorProduct.basis K b

  have hcoord : ∀ l m, algebraMap k K (b.repr (T (b l)) m) = if m = l then c else 0 := by
    intro l m
    have h1 : T.baseChange K (1 ⊗ₜ b l) = c • (1 ⊗ₜ b l) := by
      rw [h]; rfl
    rw [LinearMap.baseChange_tmul] at h1
    have h2 := congrArg (fun z => bK.repr z m) h1
    simp only [bK, Algebra.TensorProduct.basis_repr_tmul, one_smul, map_smul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul] at h2
    rw [h2]
    by_cases hml : m = l
    · subst hml; simp
    · rw [if_neg hml, if_neg (fun h => hml h.symm), map_zero, mul_zero]
  obtain ⟨l₀⟩ : Nonempty (Fin (finrank k V)) := by
    have : 0 < finrank k V := finrank_pos
    exact ⟨⟨0, this⟩⟩
  refine ⟨b.repr (T (b l₀)) l₀, ?_⟩
  apply b.ext
  intro l
  rw [LinearMap.smul_apply, Module.End.one_apply, ← b.sum_repr (T (b l))]
  rw [Finset.sum_eq_single l]
  · congr 1
    apply (algebraMap k K).injective
    rw [hcoord l l, hcoord l₀ l₀]
    simp
  · intro m _ hml
    have := hcoord l m
    rw [if_neg hml, map_eq_zero_iff _ (algebraMap k K).injective] at this
    rw [this, zero_smul]
  · intro h; exact absurd (Finset.mem_univ l) h

end BC

section Plane

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

private lemma _root_.P2mCliff.exists_generator {L : Submodule K M} (h : finrank K L = 1) :
    ∃ u : M, u ≠ 0 ∧ L = K ∙ u := by
  have hne : L ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at h; exact zero_ne_one h
  obtain ⟨u, huL, hu0⟩ := (Submodule.ne_bot_iff L).1 hne
  refine ⟨u, hu0, (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem u L).2 huL
  · rw [finrank_span_singleton hu0, h]

p2m_export "P2mCliff" "exists_generator"

lemma exists_eq_smul_one_of_three_lines (hM : finrank K M = 2) (T : Module.End K M)
    (L₁ L₂ L₃ : Submodule K M) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (hd₁ : finrank K L₁ = 1) (hd₂ : finrank K L₂ = 1) (hd₃ : finrank K L₃ = 1)
    (hT₁ : ∀ x ∈ L₁, T x ∈ L₁) (hT₂ : ∀ x ∈ L₂, T x ∈ L₂) (hT₃ : ∀ x ∈ L₃, T x ∈ L₃) :
    ∃ c : K, T = c • 1 := by
  obtain ⟨u₁, hu₁, rfl⟩ := exists_generator hd₁
  obtain ⟨u₂, hu₂, rfl⟩ := exists_generator hd₂
  obtain ⟨u₃, hu₃, rfl⟩ := exists_generator hd₃
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.1 (hT₁ u₁ (Submodule.mem_span_singleton_self u₁))
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.1 (hT₂ u₂ (Submodule.mem_span_singleton_self u₂))
  obtain ⟨c₃, hc₃⟩ := Submodule.mem_span_singleton.1 (hT₃ u₃ (Submodule.mem_span_singleton_self u₃))

  have hne : ∀ {u v : M}, u ≠ 0 → v ≠ 0 → (K ∙ u) ≠ (K ∙ v) → u ∉ K ∙ v := by
    intro u v hu hv huv hmem
    apply huv
    apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem u _).2 hmem)
    rw [finrank_span_singleton hu, finrank_span_singleton hv]
  have hli : LinearIndependent K ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hu₁, ht⟩
    · exfalso
      apply hne hu₂ hu₁ h12.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      have : t • u₂ = -(s • u₁) := eq_neg_of_add_eq_zero_right hst
      calc -(t⁻¹ * s) • u₁ = t⁻¹ • (-(s • u₁)) := by rw [neg_smul, mul_smul, smul_neg]
        _ = u₂ := by rw [← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  let bs : Basis (Fin 2) K M := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hM])
  have hbs0 : bs 0 = u₁ := by simp [bs]
  have hbs1 : bs 1 = u₂ := by simp [bs]

  set a := bs.repr u₃ 0 with ha
  set b := bs.repr u₃ 1 with hb
  have hu₃eq : u₃ = a • u₁ + b • u₂ := by
    have := (bs.sum_repr u₃).symm
    rwa [Fin.sum_univ_two, hbs0, hbs1] at this
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hne hu₃ hu₂ h23.symm
    rw [Submodule.mem_span_singleton]
    exact ⟨b, by rw [hu₃eq, ha0, zero_smul, zero_add]⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hne hu₃ hu₁ h13.symm
    rw [Submodule.mem_span_singleton]
    exact ⟨a, by rw [hu₃eq, hb0, zero_smul, add_zero]⟩

  have hTu₃ : (a * c₁) • u₁ + (b * c₂) • u₂ = (c₃ * a) • u₁ + (c₃ * b) • u₂ := by
    have h1 : T u₃ = (a * c₁) • u₁ + (b * c₂) • u₂ := by
      rw [hu₃eq, map_add, map_smul, map_smul, ← hc₁, ← hc₂, smul_smul, smul_smul]
    have h2 : T u₃ = (c₃ * a) • u₁ + (c₃ * b) • u₂ := by
      rw [← hc₃, hu₃eq, smul_add, smul_smul, smul_smul]
    rw [← h1, h2]
  have hcoef := (LinearIndependent.pair_iff.1 hli) (a * c₁ - c₃ * a) (b * c₂ - c₃ * b) (by
    rw [sub_smul, sub_smul, sub_add_sub_comm, hTu₃, sub_self])
  have h31 : c₃ = c₁ := by
    have := hcoef.1
    rw [sub_eq_zero, mul_comm] at this
    exact (mul_right_cancel₀ ha0 this).symm
  have h32 : c₃ = c₂ := by
    have := hcoef.2
    rw [sub_eq_zero, mul_comm] at this
    exact (mul_right_cancel₀ hb0 this).symm
  refine ⟨c₁, bs.ext fun i => ?_⟩
  fin_cases i
  · simp [hbs0, ← hc₁]
  · simp [hbs1, ← hc₂, ← h32, h31]

lemma finrank_eq_one_of_ne (hM : finrank K M = 2) {W : Submodule K M} (hb : W ≠ ⊥) (ht : W ≠ ⊤) :
    finrank K W = 1 := by
  have h1 : finrank K W < 2 := by
    rw [← hM, ← finrank_top K M]
    exact Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.2 ht)
  have h2 : finrank K W ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]; exact hb
  omega

end Plane

section Galois

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

lemma stab_conj {N : ℕ} [NeZero N] {ζ : Qb} (hζ : IsPrimitiveRoot ζ N)
    (g σ : Γ) (hσ : σ ζ = ζ) : (g⁻¹ * σ * g) ζ = ζ := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := g ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hi, map_pow, hσ, hi, ← AlgEquiv.mul_apply,
    inv_mul_cancel, AlgEquiv.one_apply]

lemma exists_generator_mod_stab {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    {ζ : Qb} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ∃ g₀ : Γ, ∀ γ : Γ, ∃ j : ℕ, ∃ σ : Γ, σ ζ = ζ ∧ γ = g₀ ^ j * σ := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  let f : Γ →* (ZMod (p ^ n))ˣ := hζ.autToPow ℚ
  have hf : ∀ σ : Γ, f σ = 1 → σ ζ = ζ := by
    intro σ hσ
    have h := hζ.autToPow_spec ℚ σ
    rw [show hζ.autToPow ℚ σ = 1 from hσ, Units.val_one, ZMod.val_one_eq_one_mod] at h
    rw [← h]
    by_cases hN : p ^ n = 1
    · have h1 : ζ = 1 := by simpa [hN] using hζ.pow_eq_one
      rw [h1, one_pow]
    · rw [(Nat.one_mod_eq_one).2 hN, pow_one]
  haveI : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  obtain ⟨⟨x, g₀, hg₀⟩, hx⟩ := IsCyclic.exists_generator (α := f.range)
  refine ⟨g₀, fun γ => ?_⟩
  obtain ⟨m, hm⟩ := hx ⟨f γ, γ, rfl⟩
  have hm' : x ^ m = f γ := by simpa [Subtype.ext_iff] using hm

  have ho : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
  set j : ℕ := (m % (orderOf x : ℤ)).toNat with hj
  have hjm : x ^ j = x ^ m := by
    rw [← zpow_natCast, hj, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ho.ne')),
      zpow_mod_orderOf]
  refine ⟨j, (g₀ ^ j)⁻¹ * γ, hf _ ?_, by group⟩
  rw [map_mul, map_inv, map_pow, hg₀, hjm, hm', inv_mul_cancel]

end Galois

theorem main
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (K : Type) [Field K] [Algebra k K] (W : Submodule K (ρbar.baseChange K).V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ζ = ζ →
      ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hWb, hWt⟩ := hcon

  let ρ' : Γ →* Module.End K (K ⊗[k] ρbar.V) := (ρbar.baseChange K).ρ
  have hρ' : ∀ σ : Γ, ρ' σ = (ρbar.ρ σ).baseChange K := fun _ => rfl
  have hV' : finrank K (K ⊗[k] ρbar.V) = 2 := (ρbar.baseChange K).finrank_eq
  haveI : Nontrivial ρbar.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρbar.finrank_eq]; norm_num)
  have hinv : ∀ σ : Γ, ρ' σ⁻¹ * ρ' σ = 1 := fun σ => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinj : ∀ σ : Γ, Function.Injective (ρ' σ) := by
    intro σ x y hxy
    have := congrArg (ρ' σ⁻¹) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply,
      Module.End.one_apply] at this

  have hspan : Submodule.span k (Set.range ρbar.ρ) = ⊤ :=
    (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρbar).1 habs
  have hirrK : ∀ W' : Submodule K (K ⊗[k] ρbar.V), (∀ σ : Γ, ∀ x ∈ W', ρ' σ x ∈ W') →
      W' = ⊥ ∨ W' = ⊤ := by
    intro W' hW'
    apply eq_bot_or_eq_top_of_forall_mem
    apply forall_mem_of_forall_baseChange K
    apply forall_baseChange_of_span_eq_top K hspan
    rintro _ ⟨σ, rfl⟩ x hx
    exact hW' σ x hx

  have hmapfix : ∀ σ : Γ, σ ζ = ζ → W.map (ρ' σ) = W := by
    intro σ hσ
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hW σ hσ x hx
    · intro x hx
      refine ⟨ρ' σ⁻¹ x, hW σ⁻¹ ?_ x hx, ?_⟩
      · rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact hσ.symm
      · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hmapmul : ∀ (a b : Γ) (X : Submodule K (K ⊗[k] ρbar.V)),
      X.map (ρ' (a * b)) = (X.map (ρ' b)).map (ρ' a) := by
    intro a b X
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hfin1 : ∀ (σ : Γ) (X : Submodule K (K ⊗[k] ρbar.V)), finrank K (X.map (ρ' σ)) = finrank K X :=
    fun σ X => (Submodule.equivMapOfInjective _ (hinj σ) X).finrank_eq.symm

  have hstab_map : ∀ (g : Γ) (X : Submodule K (K ⊗[k] ρbar.V)),
      (∀ σ : Γ, σ ζ = ζ → X.map (ρ' σ) = X) → ∀ σ : Γ, σ ζ = ζ → (X.map (ρ' g)).map (ρ' σ) = X.map (ρ' g) := by
    intro g X hX σ hσ
    have h := hX (g⁻¹ * σ * g) (stab_conj hζ g σ hσ)
    calc (X.map (ρ' g)).map (ρ' σ) = X.map (ρ' (σ * g)) := by rw [hmapmul]
      _ = X.map (ρ' (g * (g⁻¹ * σ * g))) := by congr 2; group
      _ = (X.map (ρ' (g⁻¹ * σ * g))).map (ρ' g) := by rw [hmapmul]
      _ = X.map (ρ' g) := by rw [h]
  have hW1 : finrank K W = 1 := finrank_eq_one_of_ne hV' hWb hWt

  obtain ⟨g₀, hg₀⟩ := exists_generator_mod_stab hp hp2 hζ
  set W' := W.map (ρ' g₀) with hW'def
  set W'' := W'.map (ρ' g₀) with hW''def
  have hW'stab : ∀ σ : Γ, σ ζ = ζ → W'.map (ρ' σ) = W' := hstab_map g₀ W hmapfix
  have hW''stab : ∀ σ : Γ, σ ζ = ζ → W''.map (ρ' σ) = W'' := hstab_map g₀ W' hW'stab
  by_cases hA : W' = W
  ·
    have hpow : ∀ j : ℕ, W.map (ρ' (g₀ ^ j)) = W := by
      intro j
      induction j with
      | zero => rw [pow_zero, map_one, Module.End.one_eq_id, Submodule.map_id]
      | succ j ih => rw [pow_succ', hmapmul, ih, ← hW'def, hA]
    have hΓ : ∀ γ : Γ, W.map (ρ' γ) = W := by
      intro γ
      obtain ⟨j, σ, hσ, rfl⟩ := hg₀ γ
      rw [hmapmul, hmapfix σ hσ, hpow j]
    rcases hirrK W (fun σ x hx => (hΓ σ).le ⟨x, hx, rfl⟩) with h | h
    · exact hWb h
    · exact hWt h
  by_cases hB : W'' = W
  ·
    let G : Subgroup Γ :=
      { carrier := {γ | W.map (ρ' γ) = W}
        one_mem' := by
          show W.map (ρ' 1) = W
          rw [map_one, Module.End.one_eq_id, Submodule.map_id]
        mul_mem' := fun {a b} ha hb => by
          show W.map (ρ' (a * b)) = W
          rw [hmapmul, hb, ha]
        inv_mem' := fun {a} ha => by
          show W.map (ρ' a⁻¹) = W
          have : W = W.map (ρ' (a⁻¹ * a)) := by
            rw [inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
          conv_lhs => rw [← ha]
          rw [← hmapmul, ← this] }
    have memG : ∀ γ : Γ, γ ∈ G ↔ W.map (ρ' γ) = W := fun γ => Iff.rfl

    have hpow2 : ∀ j : ℕ, W.map (ρ' (g₀ ^ j)) = W ∨ W.map (ρ' (g₀ ^ j)) = W' := by
      intro j
      induction j with
      | zero => left; rw [pow_zero, map_one, Module.End.one_eq_id, Submodule.map_id]
      | succ j ih =>
        rw [pow_succ', hmapmul]
        rcases ih with h | h
        · right; rw [h]
        · left; rw [h, ← hW''def, hB]
    have hclaim : ∀ γ : Γ, W.map (ρ' γ) = W ∨ W.map (ρ' γ) = W' := by
      intro γ
      obtain ⟨j, σ, hσ, rfl⟩ := hg₀ γ
      rw [hmapmul, hmapfix σ hσ]
      exact hpow2 j
    have hindex : G.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨g₀, fun b => ?_⟩
      have hbg : W.map (ρ' (b * g₀)) = W'.map (ρ' b) := by rw [hmapmul]
      by_cases hb : b ∈ G
      ·
        refine Or.inr ⟨hb, fun hbg₀ => ?_⟩
        rw [memG] at hb hbg₀
        rw [hbg] at hbg₀

        apply hA
        apply Submodule.map_injective_of_injective (hinj b)
        rw [hbg₀, hb]
      · refine Or.inl ⟨?_, hb⟩
        rw [memG] at hb ⊢
        have hbW : W.map (ρ' b) = W' := (hclaim b).resolve_left hb
        rcases hclaim (b * g₀) with h | h
        · exact h
        · exfalso
          rw [hbg] at h
          apply hA
          apply Submodule.map_injective_of_injective (hinj b)
          rw [h, hbW]
    rcases hTW K G hindex W (fun σ hσ x hx => ((memG σ).1 hσ).le ⟨x, hx, rfl⟩) with h | h
    · exact hWb h
    · exact hWt h

  have hW'W'' : W' ≠ W'' := by
    intro h
    apply hA
    apply Submodule.map_injective_of_injective (hinj g₀)
    rw [← hW'def, ← hW''def, ← h]
  have hd' : finrank K W' = 1 := by rw [hW'def, hfin1, hW1]
  have hd'' : finrank K W'' = 1 := by rw [hW''def, hfin1, hd']
  have hscalarK : ∀ σ : Γ, σ ζ = ζ → ∃ c : K, ρ' σ = c • 1 := by
    intro σ hσ
    refine exists_eq_smul_one_of_three_lines hV' (ρ' σ) W W' W'' (Ne.symm hA) (Ne.symm hB) hW'W''
      hW1 hd' hd'' ?_ ?_ ?_
    · exact fun x hx => (hmapfix σ hσ).le ⟨x, hx, rfl⟩
    · exact fun x hx => (hW'stab σ hσ).le ⟨x, hx, rfl⟩
    · exact fun x hx => (hW''stab σ hσ).le ⟨x, hx, rfl⟩
  have hscalar : ∀ σ : Γ, σ ζ = ζ → ∃ a : k, ρbar.ρ σ = a • 1 := by
    intro σ hσ
    obtain ⟨c, hc⟩ := hscalarK σ hσ
    exact exists_eq_smul_one_of_baseChange_eq_smul_one K (ρbar.ρ σ) c hc

  have hcomm : ∀ γ : Γ, ρbar.ρ γ * ρbar.ρ g₀ = ρbar.ρ g₀ * ρbar.ρ γ := by
    intro γ
    obtain ⟨j, σ, hσ, rfl⟩ := hg₀ γ
    obtain ⟨a, ha⟩ := hscalar σ hσ
    simp only [map_mul, map_pow, ha, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    rw [← pow_succ, ← pow_succ']

  have hcentral : ∀ f : Module.End k ρbar.V, f * ρbar.ρ g₀ = ρbar.ρ g₀ * f := by
    let P : Submodule k (Module.End k ρbar.V) :=
      { carrier := {f | f * ρbar.ρ g₀ = ρbar.ρ g₀ * f}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [add_mul, mul_add, ha, hb]
        smul_mem' := fun c f hf => by
          simp only [Set.mem_setOf_eq] at hf ⊢
          rw [smul_mul_assoc, mul_smul_comm, hf] }
    have h : (⊤ : Submodule k (Module.End k ρbar.V)) ≤ P := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact hcomm γ
    intro f
    exact h (Submodule.mem_top : f ∈ ⊤)
  let bV := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : k, ρbar.ρ g₀ = c₀ • 1 := by
    have hM : ∀ i j : Fin 2, Commute (Matrix.single i j (1 : k)) (LinearMap.toMatrix bV bV (ρbar.ρ g₀)) := by
      intro i j
      have h := hcentral (Matrix.toLin bV bV (Matrix.single i j 1))
      have h' := congrArg (LinearMap.toMatrix bV bV) h
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin] at h'
      exact h'
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (M := LinearMap.toMatrix bV bV (ρbar.ρ g₀)) (fun i j _ => hM i j)
    refine ⟨c, (LinearMap.toMatrix bV bV).injective ?_⟩
    rw [← hc, LinearEquiv.map_smul, LinearMap.toMatrix_one, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

  have hall : ∀ γ : Γ, ∃ a : k, ρbar.ρ γ = a • 1 := by
    intro γ
    obtain ⟨j, σ, hσ, rfl⟩ := hg₀ γ
    obtain ⟨a, ha⟩ := hscalar σ hσ
    refine ⟨c₀ ^ j * a, ?_⟩
    rw [map_mul, map_pow, hc₀, ha, smul_pow, one_pow, smul_mul_smul_comm, mul_one]
  let Sc : Submodule k (Module.End k ρbar.V) := k ∙ (1 : Module.End k ρbar.V)
  have hle : (⊤ : Submodule k (Module.End k ρbar.V)) ≤ Sc := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    obtain ⟨a, ha⟩ := hall γ
    rw [ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  have hE : Matrix.toLin bV bV (Matrix.single 0 1 (1 : k)) ∈ Sc := hle Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hE
  have := congrArg (fun f => LinearMap.toMatrix bV bV f 0 1) ha
  simp only [LinearEquiv.map_smul, LinearMap.toMatrix_one, LinearMap.toMatrix_toLin,
    Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_zero,
    Matrix.single_apply_same] at this
  exact zero_ne_one this

end P2mCliff
p2m_reactivate "P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self.P2mCliff"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self.P2mCliff"

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (K : Type) [Field K] [Algebra k K] (W : Submodule K (ρbar.baseChange K).V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ζ = ζ →
      ∀ x ∈ W, (ρbar.baseChange K).ρ σ x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  P2mCliff.main ρbar habs hTW hp2 hζ K W hW

end S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
end P2MW
export P2MW.S_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self (solution)
