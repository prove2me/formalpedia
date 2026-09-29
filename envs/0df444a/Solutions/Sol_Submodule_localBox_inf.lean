-- Prove2me | solution 1 for Submodule.localBox_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/68cd52bb-6ca9-506a-b7d2-7b672728f8a2

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_localBox_inf

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

namespace W6Chi

section Analytic

variable (v : HeightOneSpectrum (𝓞 ℚ))

noncomputable abbrev pr : ℕ := ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)

theorem pr_prime : (pr v).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

theorem mem_integers_iff_norm (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v x‖ ≤ 1 := by
  have hb := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) v
  constructor
  · intro hx; exact hb.mapsTo hx
  · intro hx
    obtain ⟨x', hx', he⟩ := hb.surjOn hx
    rw [← (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective he]
    exact hx'

theorem padicEquiv_algebraMap (r : ℚ) :
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v (algebraMap ℚ (v.adicCompletion ℚ) r) =
      (r : ℚ_[pr v]) := by
  have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v).toAlgEquiv.commutes r
  simpa using this

theorem exists_rat_sub_mem (x : v.adicCompletion ℚ) :
    ∃ r : ℚ, x - algebraMap ℚ (v.adicCompletion ℚ) r ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨r, hr⟩ := Padic.rat_dense (p := pr v) (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v x)
    zero_lt_one
  refine ⟨r, ?_⟩
  rw [mem_integers_iff_norm, map_sub, padicEquiv_algebraMap]
  exact hr.le

theorem not_dvd_den_of_mem (r : ℚ) (hr : algebraMap ℚ (v.adicCompletion ℚ) r ∈ v.adicCompletionIntegers ℚ) :
    ¬ pr v ∣ r.den := by
  rw [mem_integers_iff_norm, padicEquiv_algebraMap, Padic.eq_padicNorm] at hr
  intro hdvd
  haveI : Fact (pr v).Prime := ⟨pr_prime v⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hdvd
    exact (pr_prime v).one_lt.ne' hdvd

  have hnum : padicValInt (pr v) r.num = 0 := by
    refine padicValInt.eq_zero_of_not_dvd fun h => ?_
    have hcop := r.reduced
    have : (pr v) ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd (by exact_mod_cast Int.natAbs_dvd_natAbs.mpr h) hdvd
    rw [hcop] at this
    exact (pr_prime v).one_lt.ne' (Nat.dvd_one.mp this)
  have hden : 0 < padicValNat (pr v) r.den :=
    one_le_padicValNat_of_dvd r.den_pos.ne' hdvd |> fun h => h
  have hval : padicValRat (pr v) r < 0 := by
    rw [padicValRat, hnum]
    have : (0 : ℤ) < padicValNat (pr v) r.den := by exact_mod_cast hden
    omega
  have hnorm : (1 : ℚ) < padicNorm (pr v) r := by
    rw [padicNorm.eq_zpow_of_nonzero hr0]
    have hp : (1 : ℚ) < pr v := by exact_mod_cast (pr_prime v).one_lt
    exact one_lt_zpow₀ hp (by omega)
  have : (padicNorm (pr v) r : ℝ) ≤ 1 := hr
  have : padicNorm (pr v) r ≤ 1 := by exact_mod_cast this
  linarith

theorem mem_of_not_dvd_den (r : ℚ) (hr : ¬ pr v ∣ r.den) :
    algebraMap ℚ (v.adicCompletion ℚ) r ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff_norm, padicEquiv_algebraMap]
  exact Padic.norm_rat_le_one hr

end Analytic

section Lattice

variable {D : Type*} [Ring D] [Algebra ℚ D]

scoped instance : NoZeroSMulDivisors ℤ D := by
  refine ⟨fun {n x} h => ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    have h' : (n : ℚ) • x = 0 := by rwa [Int.cast_smul_eq_zsmul]
    exact (smul_eq_zero.mp h').resolve_left (by exact_mod_cast hn)

theorem exists_natCast_smul_mem_of_mem_span {Λ : Submodule ℤ D} {y : D}
    (hy : y ∈ Submodule.span ℚ (Λ : Set D)) :
    ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u w _ _ hu hw =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hw
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmu
    · rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : (((c.den * n : ℕ) : ℤ)) • c • u = c.num • (((n : ℕ) : ℤ) • u) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num,
        ← Int.cast_smul_eq_zsmul ℚ ((n : ℕ) : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_comm ((c.den : ℚ)) (n : ℚ), mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ hnu

theorem exists_natCast_smul_le (Λ₁ Λ₂ : Submodule ℤ D) (h₁fg : Λ₁.FG)
    (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z ∈ Λ₁, ((N : ℕ) : ℤ) • z ∈ Λ₂ := by
  classical
  obtain ⟨s, hs⟩ := h₁fg
  have hg : ∀ g : D, ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • g ∈ Λ₂ := fun g =>
    exists_natCast_smul_mem_of_mem_span (by rw [h₂sp]; exact Submodule.mem_top)
  choose n hn hnmem using hg
  refine ⟨∏ g ∈ s, n g, Finset.prod_ne_zero_iff.mpr fun g _ => hn g, fun z hz => ?_⟩
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨m, hm⟩ : n g ∣ ∏ g ∈ s, n g := Finset.dvd_prod_of_mem n hg
    rw [hm, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hnmem g)
  | zero => simp
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | smul c u _ hu => rw [smul_comm]; exact Submodule.smul_mem _ _ hu

theorem exists_basis (Λ : Submodule ℤ D) (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ D), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors ℤ Λ := ⟨fun {n x} h => by
    have h' : n • (x : D) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
    rcases smul_eq_zero.mp h' with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Subtype.ext h2)⟩
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let b₀ : Module.Basis ι ℤ Λ := Module.Free.chooseBasis ℤ Λ
  haveI : Fintype ι := inferInstance
  let n := Fintype.card ι
  let b₁ : Module.Basis (Fin n) ℤ Λ := b₀.reindex (Fintype.equivFin ι)
  let e : Fin n → D := fun i => (b₁ i : D)

  have hliZ : LinearIndependent ℤ e := b₁.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hspanZ : Submodule.span ℤ (Set.range e) = Λ := by
    have : Set.range e = Λ.subtype '' Set.range b₁ := by
      ext x; simp [e, Set.mem_range]
    rw [this, ← Submodule.map_span, b₁.span_eq, Submodule.map_top, Submodule.range_subtype]

  have hspQ : ⊤ ≤ Submodule.span ℚ (Set.range e) := by
    rw [← hsp]
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [← hspanZ] at hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hx
  exact ⟨n, Module.Basis.mk hliQ hspQ, by rw [Module.Basis.coe_mk]; exact hspanZ⟩

theorem fg_inf (Λ₁ Λ₂ : Submodule ℤ D) (h₁fg : Λ₁.FG) : (Λ₁ ⊓ Λ₂).FG := by
  haveI : IsNoetherian ℤ Λ₁ := isNoetherian_of_fg_of_noetherian _ h₁fg
  have h : ((Λ₁ ⊓ Λ₂).comap Λ₁.subtype).FG := IsNoetherian.noetherian _
  have := h.map Λ₁.subtype
  rw [Submodule.map_comap_subtype] at this
  have heq : Λ₁ ⊓ (Λ₁ ⊓ Λ₂) = Λ₁ ⊓ Λ₂ := by rw [← inf_assoc, inf_idem]
  rwa [heq] at this

end Lattice

section Coord

variable {D : Type*} [Ring D] [Algebra ℚ D] (v : HeightOneSpectrum (𝓞 ℚ))
variable {n : ℕ} (b : Module.Basis (Fin n) ℚ D)

noncomputable def ψ (i : Fin n) : D ⊗[ℚ] v.adicCompletion ℚ →ₗ[ℚ] v.adicCompletion ℚ :=
  (TensorProduct.lid ℚ (v.adicCompletion ℚ)).toLinearMap ∘ₗ (b.coord i).rTensor (v.adicCompletion ℚ)

theorem ψ_tmul (i : Fin n) (z : D) (c : v.adicCompletion ℚ) : ψ v b i (z ⊗ₜ c) = (b.repr z i) • c := by
  simp [ψ]

theorem ψ_sum (i : Fin n) (c : Fin n → v.adicCompletion ℚ) : ψ v b i (∑ j, b j ⊗ₜ[ℚ] c j) = c i := by
  simp only [map_sum, ψ_tmul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

theorem sum_tmul_eq_sum_basis_tmul {m : ℕ} (f : Fin m → D) (d : Fin m → v.adicCompletion ℚ) :
    ∑ j, f j ⊗ₜ[ℚ] d j = ∑ i, b i ⊗ₜ[ℚ] (∑ j, (b.repr (f j) i) • d j) := by
  have hf : ∀ j, f j = ∑ i, (b.repr (f j) i) • b i := fun j => (b.sum_repr (f j)).symm
  conv_lhs => arg 2; ext j; rw [hf j]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  exact Finset.sum_comm

theorem ψ_eq_sum_repr_smul {m : ℕ} (f : Module.Basis (Fin m) ℚ D) (c : Fin n → v.adicCompletion ℚ) (j : Fin m) :
    ψ v f j (∑ i, b i ⊗ₜ[ℚ] c i) = ∑ i, (f.repr (b i) j) • c i := by
  simp only [map_sum, ψ_tmul]

end Coord

section Global

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem int_of_forall_sum_mul_repr {n m₁ m₂ : ℕ} (b : Module.Basis (Fin n) ℚ D)
    (f₁ : Module.Basis (Fin m₁) ℚ D) (f₂ : Module.Basis (Fin m₂) ℚ D)
    (hM : Submodule.span ℤ (Set.range f₁) ⊓ Submodule.span ℤ (Set.range f₂) ≤ Submodule.span ℤ (Set.range b))
    (q : Fin n → ℚ)
    (h₁ : ∀ j, ∑ i, f₁.repr (b i) j * q i ∈ Set.range (Int.cast : ℤ → ℚ))
    (h₂ : ∀ j, ∑ i, f₂.repr (b i) j * q i ∈ Set.range (Int.cast : ℤ → ℚ)) :
    ∀ i, q i ∈ Set.range (Int.cast : ℤ → ℚ) := by
  set y : D := ∑ i, q i • b i with hy
  have hrepr : ∀ {m : ℕ} (f : Module.Basis (Fin m) ℚ D) (j : Fin m), f.repr y j = ∑ i, f.repr (b i) j * q i := by
    intro m f j
    simp only [hy, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hy₁ : y ∈ Submodule.span ℤ (Set.range f₁) := by
    rw [Module.Basis.mem_span_iff_repr_mem ℤ f₁ y]
    intro j; rw [hrepr]; simpa using h₁ j
  have hy₂ : y ∈ Submodule.span ℤ (Set.range f₂) := by
    rw [Module.Basis.mem_span_iff_repr_mem ℤ f₂ y]
    intro j; rw [hrepr]; simpa using h₂ j
  have hyb := hM ⟨hy₁, hy₂⟩
  rw [Module.Basis.mem_span_iff_repr_mem ℤ b y] at hyb
  intro i
  have := hyb i
  have hq : b.repr y i = q i := by
    simp only [hy, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [eq_comm]
  rw [hq] at this
  simpa using this

end Global

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem mem_integers_of_forall {n : ℕ} {J : Type} [Fintype J] (A : J → Fin n → ℤ)
    (hG : ∀ q : Fin n → ℚ, (∀ j, ∑ i, (A j i : ℚ) * q i ∈ Set.range (Int.cast : ℤ → ℚ)) →
      ∀ i, q i ∈ Set.range (Int.cast : ℤ → ℚ))
    (c : Fin n → v.adicCompletion ℚ)
    (hc : ∀ j, ∑ i, ((A j i : ℤ) : ℚ) • c i ∈ v.adicCompletionIntegers ℚ) :
    ∀ i, c i ∈ v.adicCompletionIntegers ℚ := by
  classical

  choose r hr using fun i => exists_rat_sub_mem v (c i)

  set t : J → ℚ := fun j => ∑ i, (A j i : ℚ) * r i with ht
  have htint : ∀ j, algebraMap ℚ (v.adicCompletion ℚ) (t j) ∈ v.adicCompletionIntegers ℚ := by
    intro j
    have h1 : algebraMap ℚ (v.adicCompletion ℚ) (t j) =
        ∑ i, ((A j i : ℤ) : ℚ) • c i - ∑ i, (A j i : ℤ) • (c i - algebraMap ℚ (v.adicCompletion ℚ) (r i)) := by
      simp only [ht, map_sum, map_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul, smul_sub, sub_sub_cancel, zsmul_eq_mul, map_intCast]
    rw [h1]
    refine sub_mem (hc j) (sum_mem fun i _ => zsmul_mem (hr i) _)
  have htden : ∀ j, ¬ pr v ∣ (t j).den := fun j => not_dvd_den_of_mem v (t j) (htint j)

  set s : ℕ := ∏ j, (t j).den with hs
  have hs0 : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (t j).den_nz
  have hps : ¬ pr v ∣ s := by
    rw [hs]
    intro h
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp (pr_prime v)) _).mp h
    exact htden j hj

  have hst : ∀ j, ∑ i, (A j i : ℚ) * (s * r i) ∈ Set.range (Int.cast : ℤ → ℚ) := by
    intro j
    have : ∑ i, (A j i : ℚ) * (s * r i) = s * t j := by
      rw [ht]; simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    obtain ⟨m, hm⟩ : (t j).den ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    refine ⟨m * (t j).num, ?_⟩
    have hsq : (s : ℚ) = ((t j).den : ℚ) * (m : ℚ) := by rw [hm]; push_cast; ring
    have h2 : t j * ((t j).den : ℚ) = ((t j).num : ℚ) := Rat.mul_den_eq_num (t j)
    rw [hsq]
    push_cast
    linear_combination (-(m : ℚ)) * h2

  have hr_int : ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (r i) ∈ v.adicCompletionIntegers ℚ := by
    intro i
    obtain ⟨m, hm⟩ := hG (fun i => s * r i) hst i
    have hri : r i = (m : ℚ) * ((s : ℚ))⁻¹ := by
      have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs0
      have hm' : (m : ℚ) = s * r i := hm
      field_simp
      linear_combination -hm'
    rw [hri, map_mul, map_intCast]
    refine mul_mem (intCast_mem _ m) (mem_of_not_dvd_den v _ ?_)
    rw [Rat.inv_natCast_den, if_neg hs0]
    exact hps
  intro i
  have : c i = (c i - algebraMap ℚ (v.adicCompletion ℚ) (r i)) + algebraMap ℚ (v.adicCompletion ℚ) (r i) := by ring
  rw [this]
  exact add_mem (hr i) (hr_int i)

end Local

section Main

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem main (Λ₁ Λ₂ : Submodule ℤ D)
    (h₁fg : Λ₁.FG) (h₁sp : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (h₂fg : Λ₂.FG) (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Λ₁ ⊓ Λ₂) v = Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ₂ v := by
  classical
  refine le_antisymm (le_inf (localBox_mono inf_le_left v) (localBox_mono inf_le_right v)) ?_

  obtain ⟨N, hN0, hN⟩ := exists_natCast_smul_le Λ₁ Λ₂ h₁fg h₂sp
  have hMfg : (Λ₁ ⊓ Λ₂).FG := fg_inf Λ₁ Λ₂ h₁fg
  have hMsp : Submodule.span ℚ ((Λ₁ ⊓ Λ₂ : Submodule ℤ D) : Set D) = ⊤ := by
    rw [eq_top_iff, ← h₁sp]
    refine Submodule.span_le.mpr fun z hz => ?_
    have hNz : ((N : ℕ) : ℤ) • z ∈ Λ₁ ⊓ Λ₂ := ⟨Submodule.smul_mem _ _ hz, hN z hz⟩
    have : z = ((N : ℚ))⁻¹ • ((N : ℚ) • z) := by
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN0), one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have : (N : ℚ) • z = ((N : ℕ) : ℤ) • z := by
      rw [← Int.cast_smul_eq_zsmul ℚ]; norm_cast
    rw [this]; exact hNz

  obtain ⟨n, E, hE⟩ := exists_basis (Λ₁ ⊓ Λ₂) hMfg hMsp
  obtain ⟨m₁, F₁, hF₁⟩ := exists_basis Λ₁ h₁fg h₁sp
  obtain ⟨m₂, F₂, hF₂⟩ := exists_basis Λ₂ h₂fg h₂sp

  have hA : ∀ (k : Fin 2), True := fun _ => trivial
  have hE₁ : ∀ i j, ∃ z : ℤ, (z : ℚ) = F₁.repr (E i) j := by
    intro i j
    have hi : E i ∈ Submodule.span ℤ (Set.range F₁) := by
      rw [hF₁]; exact (hE ▸ Submodule.subset_span (Set.mem_range_self i) : E i ∈ Λ₁ ⊓ Λ₂).1
    obtain ⟨z, hz⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ F₁ (E i)).mp hi j
    exact ⟨z, by simpa using hz⟩
  have hE₂ : ∀ i j, ∃ z : ℤ, (z : ℚ) = F₂.repr (E i) j := by
    intro i j
    have hi : E i ∈ Submodule.span ℤ (Set.range F₂) := by
      rw [hF₂]; exact (hE ▸ Submodule.subset_span (Set.mem_range_self i) : E i ∈ Λ₁ ⊓ Λ₂).2
    obtain ⟨z, hz⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ F₂ (E i)).mp hi j
    exact ⟨z, by simpa using hz⟩
  choose A₁ hA₁ using hE₁
  choose A₂ hA₂ using hE₂
  let A : (Fin m₁ ⊕ Fin m₂) → Fin n → ℤ := fun j i => Sum.elim (fun j => A₁ i j) (fun j => A₂ i j) j

  have hG : ∀ q : Fin n → ℚ, (∀ j, ∑ i, (A j i : ℚ) * q i ∈ Set.range (Int.cast : ℤ → ℚ)) →
      ∀ i, q i ∈ Set.range (Int.cast : ℤ → ℚ) := by
    intro q hq
    refine int_of_forall_sum_mul_repr E F₁ F₂ (by rw [hF₁, hF₂, hE]) q (fun j => ?_) (fun j => ?_)
    · have := hq (Sum.inl j); simpa [A, hA₁] using this
    · have := hq (Sum.inr j); simpa [A, hA₂] using this

  intro x hx
  obtain ⟨d₁, hd₁, hx₁⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul F₁ Λ₁ hF₁ v x).mp hx.1
  obtain ⟨d₂, hd₂, hx₂⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul F₂ Λ₂ hF₂ v x).mp hx.2
  let c : Fin n → v.adicCompletion ℚ := fun i => ∑ j, (E.repr (F₁ j) i) • d₁ j
  have hxc : x = ∑ i, E i ⊗ₜ[ℚ] c i := hx₁.trans (sum_tmul_eq_sum_basis_tmul v E F₁ d₁)

  have hc₁ : ∀ j, ∑ i, ((A₁ i j : ℤ) : ℚ) • c i ∈ v.adicCompletionIntegers ℚ := by
    intro j
    have : ∑ i, ((A₁ i j : ℤ) : ℚ) • c i = d₁ j := by
      simp only [hA₁]
      rw [← ψ_eq_sum_repr_smul v E F₁ c j, ← hxc, hx₁, ψ_sum]
    rw [this]; exact hd₁ j
  have hc₂ : ∀ j, ∑ i, ((A₂ i j : ℤ) : ℚ) • c i ∈ v.adicCompletionIntegers ℚ := by
    intro j
    have : ∑ i, ((A₂ i j : ℤ) : ℚ) • c i = d₂ j := by
      simp only [hA₂]
      rw [← ψ_eq_sum_repr_smul v E F₂ c j, ← hxc, hx₂, ψ_sum]
    rw [this]; exact hd₂ j
  have hcint : ∀ i, c i ∈ v.adicCompletionIntegers ℚ :=
    mem_integers_of_forall v A hG c fun j => by
      cases j with
      | inl j => simpa [A] using hc₁ j
      | inr j => simpa [A] using hc₂ j
  exact (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul E (Λ₁ ⊓ Λ₂) hE v x).mpr ⟨c, hcint, hxc⟩

end Main

end W6Chi
p2m_reactivate "P2MW.S_Submodule_localBox_inf.W6Chi"

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ₁ Λ₂ : Submodule ℤ D)
    (h₁fg : Λ₁.FG) (h₁sp : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (h₂fg : Λ₂.FG) (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Submodule.localBox (Λ₁ ⊓ Λ₂) v = Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ₂ v :=
  W6Chi.main Λ₁ Λ₂ h₁fg h₁sp h₂fg h₂sp v

end S_Submodule_localBox_inf
end P2MW
export P2MW.S_Submodule_localBox_inf (solution)
