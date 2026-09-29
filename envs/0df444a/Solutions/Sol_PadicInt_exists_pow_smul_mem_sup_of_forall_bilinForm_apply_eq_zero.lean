-- Prove2me | solution 1 for PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/34ccb7b1-2af5-5695-9895-469d51509133

import Mathlib
import Theorems.Thm_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero

set_option autoImplicit false

open scoped TensorProduct

namespace TateDuality

section Denominators

variable {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

theorem exists_smul_eq_one_tmul_of_mem_baseChange (N : Submodule ℤ_[p] T) {w : ℚ_[p] ⊗[ℤ_[p]] T}
    (hw : w ∈ N.baseChange ℚ_[p]) :
    ∃ s : nonZeroDivisors ℤ_[p], ∃ n ∈ N, (s : ℤ_[p]) • w = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] n := by
  have hw' : w ∈ LinearMap.range (N.subtype.baseChange ℚ_[p]) := hw
  obtain ⟨w₀, rfl⟩ := LinearMap.mem_range.1 hw'
  obtain ⟨⟨n, s⟩, hs⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (TensorProduct.mk ℤ_[p] ℚ_[p] N 1) w₀
  refine ⟨s, n, n.2, ?_⟩
  have h := congrArg (N.subtype.baseChange ℚ_[p]) hs
  rw [Submonoid.smul_def, LinearMap.map_smul_of_tower, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
    Submodule.subtype_apply] at h
  exact h

theorem exists_nonZeroDivisor_smul_mem_of_one_tmul_mem_baseChange (N : Submodule ℤ_[p] T) {z : T}
    (hz : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] z ∈ N.baseChange ℚ_[p]) :
    ∃ s : nonZeroDivisors ℤ_[p], (s : ℤ_[p]) • z ∈ N := by
  obtain ⟨s, n, hn, hs⟩ := exists_smul_eq_one_tmul_of_mem_baseChange N hz
  have h0 : TensorProduct.mk ℤ_[p] ℚ_[p] T 1 ((s : ℤ_[p]) • z - n) = 0 := by
    rw [TensorProduct.mk_apply, TensorProduct.tmul_sub, TensorProduct.tmul_smul, hs, sub_self]
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p]) _).1 h0
  refine ⟨s' * s, ?_⟩
  rw [Submonoid.smul_def, smul_sub, sub_eq_zero] at hs'
  rw [Submonoid.coe_mul, mul_smul, hs']
  exact N.smul_mem _ hn

theorem exists_pow_smul_mem_of_nonZeroDivisor_smul_mem [Module.Finite ℤ_[p] T] (N : Submodule ℤ_[p] T) :
    ∃ k : ℕ, ∀ v : T, (∃ s : nonZeroDivisors ℤ_[p], (s : ℤ_[p]) • v ∈ N) → ((p : ℤ_[p]) ^ k) • v ∈ N := by
  classical

  have hfg : (Submodule.torsion ℤ_[p] (T ⧸ N)).FG := IsNoetherian.noetherian _
  obtain ⟨S, hS⟩ := hfg

  have hgen : ∀ q ∈ S, ∃ a : nonZeroDivisors ℤ_[p], (a : ℤ_[p]) • q = 0 := by
    intro q hq
    have : q ∈ Submodule.torsion ℤ_[p] (T ⧸ N) := hS ▸ Submodule.subset_span hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 this
    exact ⟨a, by simpa [Submonoid.smul_def] using ha⟩
  choose! a ha using hgen
  set A : ℤ_[p] := ∏ q ∈ S, (a q : ℤ_[p]) with hA
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro q hq
    exact nonZeroDivisors.coe_ne_zero (a q)

  have hkill : ∀ q ∈ Submodule.torsion ℤ_[p] (T ⧸ N), A • q = 0 := by
    intro q hq
    rw [← hS] at hq
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · intro q hq
      obtain ⟨B, hB⟩ : (a q : ℤ_[p]) ∣ A := Finset.dvd_prod_of_mem _ hq
      rw [hB, mul_comm, mul_smul, ha q hq, smul_zero]
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_comm, hx, smul_zero]

  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ q : T ⧸ N, A • q = 0 → ((p : ℤ_[p]) ^ k) • q = 0 := by
    refine ⟨A.valuation, fun q hq => ?_⟩
    have hu := PadicInt.unitCoeff_spec hA0
    have : ((p : ℤ_[p]) ^ A.valuation) = ((PadicInt.unitCoeff hA0)⁻¹ : ℤ_[p]ˣ) • A := by
      rw [Units.smul_def, smul_eq_mul]
      calc ((p : ℤ_[p]) ^ A.valuation)
          = (((PadicInt.unitCoeff hA0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
              ((PadicInt.unitCoeff hA0 : ℤ_[p]) * (p : ℤ_[p]) ^ A.valuation) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = _ := by rw [← hu]
    rw [this, smul_assoc, hq, smul_zero]
  refine ⟨k, fun v hv => ?_⟩
  obtain ⟨s, hs⟩ := hv
  have hq : Submodule.Quotient.mk (p := N) v ∈ Submodule.torsion ℤ_[p] (T ⧸ N) := by
    rw [Submodule.mem_torsion_iff]
    refine ⟨s, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hs
  have := hk _ (hkill _ hq)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end Denominators

end TateDuality

namespace TateDuality

section BaseChange

variable {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

noncomputable def repBaseChange {Γ : Type*} [Monoid Γ] (ρ : Γ →* Module.End ℤ_[p] T) :
    Representation ℚ_[p] Γ (ℚ_[p] ⊗[ℤ_[p]] T) where
  toFun γ := (ρ γ).baseChange ℚ_[p]
  map_one' := by
    show (ρ 1).baseChange ℚ_[p] = 1
    rw [map_one]
    exact LinearMap.baseChange_one ℤ_[p] T
  map_mul' a b := by
    show (ρ (a * b)).baseChange ℚ_[p] = (ρ a).baseChange ℚ_[p] * (ρ b).baseChange ℚ_[p]
    rw [map_mul]
    exact LinearMap.baseChange_mul (ρ a) (ρ b)

@[scoped simp] theorem repBaseChange_apply_tmul {Γ : Type*} [Monoid Γ] (ρ : Γ →* Module.End ℤ_[p] T) (γ : Γ)
    (c : ℚ_[p]) (x : T) : repBaseChange ρ γ (c ⊗ₜ[ℤ_[p]] x) = c ⊗ₜ[ℤ_[p]] ρ γ x :=
  LinearMap.baseChange_tmul _ _ _

noncomputable def charBaseChange {Γ : Type*} [Monoid Γ] (χ : Γ →* ℤ_[p]ˣ) : Γ →* ℚ_[p]ˣ :=
  (Units.map ((algebraMap ℤ_[p] ℚ_[p] : ℤ_[p] →+* ℚ_[p]) : ℤ_[p] →* ℚ_[p])).comp χ

@[scoped simp] theorem charBaseChange_coe {Γ : Type*} [Monoid Γ] (χ : Γ →* ℤ_[p]ˣ) (γ : Γ) :
    ((charBaseChange χ γ : ℚ_[p]ˣ) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] ((χ γ : ℤ_[p]ˣ) : ℤ_[p]) := rfl

noncomputable def unitBaseChange (D : (Module.End ℤ_[p] T)ˣ) :
    (ℚ_[p] ⊗[ℤ_[p]] T) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T) :=
  LinearEquiv.ofLinear ((D : Module.End ℤ_[p] T).baseChange ℚ_[p]) ((↑D⁻¹ : Module.End ℤ_[p] T).baseChange ℚ_[p])
    (by rw [← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, Units.mul_inv, LinearMap.baseChange_one]; rfl)
    (by rw [← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, Units.inv_mul, LinearMap.baseChange_one]; rfl)

@[scoped simp] theorem unitBaseChange_apply (D : (Module.End ℤ_[p] T)ˣ) (w : ℚ_[p] ⊗[ℤ_[p]] T) :
    unitBaseChange D w = (D : Module.End ℤ_[p] T).baseChange ℚ_[p] w := rfl

theorem bilin_ext {B B' : LinearMap.BilinForm ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)}
    (h : ∀ (c : ℚ_[p]) (x : T) (c' : ℚ_[p]) (y : T),
      B (c ⊗ₜ[ℤ_[p]] x) (c' ⊗ₜ[ℤ_[p]] y) = B' (c ⊗ₜ[ℤ_[p]] x) (c' ⊗ₜ[ℤ_[p]] y)) : B = B' :=
  TensorProduct.AlgebraTensorModule.ext fun c x =>
    TensorProduct.AlgebraTensorModule.ext fun c' y => h c x c' y

theorem mem_baseChange_of_forall_mem (N N' : Submodule ℤ_[p] T) (f : T →ₗ[ℤ_[p]] T)
    (hf : ∀ x ∈ N, f x ∈ N') : ∀ w ∈ N.baseChange ℚ_[p], f.baseChange ℚ_[p] w ∈ N'.baseChange ℚ_[p] := by
  have hle : N.baseChange ℚ_[p] ≤ (N'.baseChange ℚ_[p]).comap (f.baseChange ℚ_[p]) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply, LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hf x hx)
  exact fun w hw => hle hw

theorem baseChange_apply_eq_zero (e : LinearMap.BilinForm ℤ_[p] T) (N N' : Submodule ℤ_[p] T)
    (h : ∀ x ∈ N, ∀ y ∈ N', e x y = 0) :
    ∀ w ∈ N.baseChange ℚ_[p], ∀ w' ∈ N'.baseChange ℚ_[p], e.baseChange ℚ_[p] w w' = 0 := by
  intro w hw w' hw'
  rw [Submodule.baseChange_eq_span] at hw hw'
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    induction hw' using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨y, hy, rfl⟩ := hw'
      rw [TensorProduct.mk_apply, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, h x hx y hy, zero_smul]
    | zero => rw [map_zero]
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul c w₁ _ h₁ => rw [map_smul, h₁, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
  | smul c w₁ _ h₁ => rw [map_smul, LinearMap.smul_apply, h₁, smul_zero]

theorem baseChange_sep_of_sep (e : LinearMap.BilinForm ℤ_[p] T) (N : Submodule ℤ_[p] T)
    (h : ∀ y ∈ N, (∀ y' ∈ N, e y y' = 0) → y = 0) :
    ∀ w ∈ N.baseChange ℚ_[p], (∀ w' ∈ N.baseChange ℚ_[p], e.baseChange ℚ_[p] w w' = 0) → w = 0 := by
  intro w hw hw'
  obtain ⟨s, n, hn, hs⟩ := exists_smul_eq_one_tmul_of_mem_baseChange N hw
  have hn0 : n = 0 := by
    refine h n hn fun y' hy' => ?_
    have h1 := hw' _ (Submodule.tmul_mem_baseChange_of_mem (1 : ℚ_[p]) hy')
    have h2 : e.baseChange ℚ_[p] ((s : ℤ_[p]) • w) ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y') = 0 := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, h1, smul_zero]
    rw [hs, LinearMap.BilinForm.baseChange_tmul, mul_one, ← Algebra.algebraMap_eq_smul_one] at h2
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).1 h2
  rw [hn0, TensorProduct.tmul_zero, ← algebraMap_smul ℚ_[p], smul_eq_zero] at hs
  exact hs.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).2
    (nonZeroDivisors.coe_ne_zero s))

theorem exists_pow_smul_mem_sup_of_forall_apply_eq_zero [Module.Finite ℤ_[p] T] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Module.End ℤ_[p] T) (χ : Γ →* ℤ_[p]ˣ) (I : Subgroup Γ)
    (e : LinearMap.BilinForm ℤ_[p] T)
    (hskew : ∀ a b : T, e a b = - e b a)
    (hnondeg : ∀ a : T, (∀ b : T, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : T), e (ρ γ a) (ρ γ b) = ((χ γ : ℤ_[p]ˣ) : ℤ_[p]) * e a b)
    (Tt To : Submodule ℤ_[p] T)
    (hTt : ∀ γ ∈ I, ∀ x ∈ Tt, ρ γ x ∈ Tt)
    (hTo : ∀ γ ∈ I, ∀ y ∈ To, ρ γ y ∈ To)
    (hISO : ∀ x ∈ Tt, ∀ y ∈ To, e x y = 0)
    (hCUT : ∃ k : ℕ, ∀ τ ∈ I, ∀ v : T, ((p : ℤ_[p]) ^ k) • (ρ τ v - v) ∈ Tt ⊔ To)
    (hOLD : ∀ y ∈ To, (∀ y' ∈ To, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    ∃ k : ℕ, ∀ v : T, (∀ x ∈ Tt, e v x = 0) → ((p : ℤ_[p]) ^ k) • v ∈ Tt ⊔ To := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_of_nonZeroDivisor_smul_mem (Tt ⊔ To)
  refine ⟨k, fun v hv => hk _ ?_⟩
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]

  have hskewK : ∀ a b : ℚ_[p] ⊗[ℤ_[p]] T, e.baseChange ℚ_[p] a b = - e.baseChange ℚ_[p] b a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | tmul c x =>
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
      | tmul c' y => rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hskew x y,
          neg_smul, mul_comm]
      | add b b' hb hb' => rw [map_add, map_add, LinearMap.add_apply, hb, hb', neg_add]
    | add a a' ha ha' => rw [map_add, LinearMap.add_apply, map_add, ha, ha', neg_add]
  have hreflK : ∀ a b : ℚ_[p] ⊗[ℤ_[p]] T, e.baseChange ℚ_[p] a b = 0 → e.baseChange ℚ_[p] b a = 0 :=
    fun a b h => by rw [hskewK, h, neg_zero]
  have hnondegK : ∀ a : ℚ_[p] ⊗[ℤ_[p]] T, (∀ b, e.baseChange ℚ_[p] a b = 0) → a = 0 := by
    intro a ha
    refine baseChange_sep_of_sep e ⊤ (fun y _ hy => hnondeg y fun b => hy b trivial) a ?_ (fun b _ => ha b)
    rw [Submodule.baseChange_top]; trivial
  have hequivK : ∀ (γ : Γ) (a b : ℚ_[p] ⊗[ℤ_[p]] T),
      e.baseChange ℚ_[p] (repBaseChange ρ γ a) (repBaseChange ρ γ b)
        = ((charBaseChange χ γ : ℚ_[p]ˣ) : ℚ_[p]) * e.baseChange ℚ_[p] a b := by
    intro γ
    have hforms : (e.baseChange ℚ_[p]).compl₁₂ (repBaseChange ρ γ) (repBaseChange ρ γ)
        = ((charBaseChange χ γ : ℚ_[p]ˣ) : ℚ_[p]) • e.baseChange ℚ_[p] := by
      refine bilin_ext fun c x c' y => ?_
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, repBaseChange_apply_tmul,
        LinearMap.BilinForm.baseChange_tmul, hequiv, charBaseChange_coe, Algebra.smul_def, map_mul,
        Algebra.algebraMap_self_apply]
      ring
    intro a b
    have h := LinearMap.congr_fun₂ hforms a b
    rw [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  have hVtK : ∀ γ ∈ I, ∀ w ∈ Tt.baseChange ℚ_[p], repBaseChange ρ γ w ∈ Tt.baseChange ℚ_[p] :=
    fun γ hγ => mem_baseChange_of_forall_mem Tt Tt (ρ γ) (hTt γ hγ)
  have hVoK : ∀ γ ∈ I, ∀ w ∈ To.baseChange ℚ_[p], repBaseChange ρ γ w ∈ To.baseChange ℚ_[p] :=
    fun γ hγ => mem_baseChange_of_forall_mem To To (ρ γ) (hTo γ hγ)
  have hISOK := baseChange_apply_eq_zero (p := p) e Tt To hISO
  have hCUTK : ∀ τ ∈ I, ∀ w : ℚ_[p] ⊗[ℤ_[p]] T,
      repBaseChange ρ τ w - w ∈ Tt.baseChange ℚ_[p] ⊔ To.baseChange ℚ_[p] := by
    obtain ⟨k₀, hk₀⟩ := hCUT
    intro τ hτ w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
    | tmul c x =>
      rw [repBaseChange_apply_tmul, ← TensorProduct.tmul_sub]
      have hp0 : algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ k₀) ≠ 0 :=
        (map_ne_zero_iff _ hinj).2 (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
      have hc : c ⊗ₜ[ℤ_[p]] (ρ τ x - x)
          = (c * (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ k₀))⁻¹) ⊗ₜ[ℤ_[p]] (((p : ℤ_[p]) ^ k₀) • (ρ τ x - x)) := by
        rw [TensorProduct.tmul_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ k₀), TensorProduct.smul_tmul',
          smul_eq_mul, mul_comm c, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
      obtain ⟨t, ht, o, ho, hto⟩ := Submodule.mem_sup.1 (hk₀ τ hτ x)
      rw [hc, ← hto, TensorProduct.tmul_add]
      exact Submodule.add_mem_sup (Submodule.tmul_mem_baseChange_of_mem _ ht)
        (Submodule.tmul_mem_baseChange_of_mem _ ho)
    | add w w' hw hw' =>
      have h : repBaseChange ρ τ (w + w') - (w + w') = (repBaseChange ρ τ w - w) + (repBaseChange ρ τ w' - w') := by
        rw [map_add]; abel
      rw [h]
      exact Submodule.add_mem _ hw hw'
  have hOLDK := baseChange_sep_of_sep (p := p) e To hOLD
  have hCYCK : ∃ τ₀ ∈ I, charBaseChange χ τ₀ ≠ 1 := by
    obtain ⟨τ₀, hτ₀, hne⟩ := hCYC
    refine ⟨τ₀, hτ₀, fun h => hne (Units.ext (hinj ?_))⟩
    have h' := congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p])) h
    simp only [charBaseChange_coe, Units.val_one] at h'
    rw [h', Units.val_one, map_one]
  have hle := LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
    (repBaseChange ρ) (charBaseChange χ) I (e.baseChange ℚ_[p]) hreflK hnondegK hequivK
    (Tt.baseChange ℚ_[p]) (To.baseChange ℚ_[p]) hVtK hVoK hISOK hCUTK hOLDK hCYCK

  have hmem : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] v ∈ (e.baseChange ℚ_[p]).orthogonal (Tt.baseChange ℚ_[p]) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    try rw [LinearMap.BilinForm.isOrtho_def]
    refine hreflK _ _ ?_
    rw [Submodule.baseChange_eq_span] at hn
    induction hn using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      rw [TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, hv x hx, zero_smul]
    | zero => rw [map_zero]
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul c w₁ _ h₁ => rw [map_smul, h₁, smul_zero]
  have hle' : Tt.baseChange ℚ_[p] ⊔ To.baseChange ℚ_[p] ≤ (Tt ⊔ To).baseChange ℚ_[p] :=
    sup_le (Submodule.baseChange_mono _ le_sup_left) (Submodule.baseChange_mono _ le_sup_right)
  exact exists_nonZeroDivisor_smul_mem_of_one_tmul_mem_baseChange _ (hle' (hle hmem))

end BaseChange

end TateDuality
p2m_reactivate "P2MW.S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero.TateDuality"

theorem solution
    {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Module.End ℤ_[p] T) (χ : Γ →* ℤ_[p]ˣ) (I : Subgroup Γ)
    (e : LinearMap.BilinForm ℤ_[p] T)
    (hskew : ∀ a b : T, e a b = - e b a)
    (hnondeg : ∀ a : T, (∀ b : T, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : T), e (ρ γ a) (ρ γ b) = ((χ γ : ℤ_[p]ˣ) : ℤ_[p]) * e a b)
    (Tt To : Submodule ℤ_[p] T)
    (hTt : ∀ γ ∈ I, ∀ x ∈ Tt, ρ γ x ∈ Tt)
    (hTo : ∀ γ ∈ I, ∀ y ∈ To, ρ γ y ∈ To)
    (hISO : ∀ x ∈ Tt, ∀ y ∈ To, e x y = 0)
    (hCUT : ∃ k : ℕ, ∀ τ ∈ I, ∀ v : T, ((p : ℤ_[p]) ^ k) • (ρ τ v - v) ∈ Tt ⊔ To)
    (hOLD : ∀ y ∈ To, (∀ y' ∈ To, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    ∃ k : ℕ, ∀ v : T, (∀ x ∈ Tt, e v x = 0) → ((p : ℤ_[p]) ^ k) • v ∈ Tt ⊔ To :=
  TateDuality.exists_pow_smul_mem_sup_of_forall_apply_eq_zero ρ χ I e hskew hnondeg hequiv Tt To hTt hTo hISO hCUT hOLD hCYC

end S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero
end P2MW
export P2MW.S_PadicInt_exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero (solution)
