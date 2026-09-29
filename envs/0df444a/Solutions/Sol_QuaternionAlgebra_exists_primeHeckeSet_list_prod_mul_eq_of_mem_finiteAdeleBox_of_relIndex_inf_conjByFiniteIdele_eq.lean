-- Prove2me | solution 1 for QuaternionAlgebra.exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c02494af-6184-545b-b9a5-550c7a1d8f48

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_conj_diagonal
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

namespace ListProdEval

theorem map_prod_map_eq_pow_count {α M N : Type*} [DecidableEq α] [Monoid M] [Monoid N]
    (f : M →* N) (t : α → M) (a₀ : α) :
    ∀ (L : List α), (∀ a ∈ L, a ≠ a₀ → f (t a) = 1) → f (L.map t).prod = (f (t a₀)) ^ (L.count a₀)
  | [], _ => by simp
  | (a :: L), h => by
    have ih := map_prod_map_eq_pow_count f t a₀ L (fun b hb hne => h b (List.mem_cons_of_mem a hb) hne)
    rw [List.map_cons, List.prod_cons, map_mul, ih, List.count_cons]
    by_cases ha : a = a₀
    · subst ha
      simp [pow_succ']
    · rw [h a List.mem_cons_self ha, one_mul]
      simp [beq_iff_eq, ha]

theorem map_prod_map_eq_one {α M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) (t : α → M) (L : List α) (h : ∀ a ∈ L, f (t a) = 1) : f (L.map t).prod = 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), one_mul]

end ListProdEval

namespace QFactAsm

open IsDedekindDomain NumberField

section Generic
variable {K : Type*} [Field K] (O : ValuationSubring K)

def IsInt (M : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, M i j ∈ O

theorem IsInt.mul {M N : Matrix (Fin 2) (Fin 2) K} (hM : IsInt O M) (hN : IsInt O N) : IsInt O (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.toSubring.sum_mem fun k _ => O.toSubring.mul_mem (hM i k) (hN k j)

def diagGL (x : K) (hx : x ≠ 0) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![(1 : K), x], Matrix.diagonal ![(1 : K), x⁻¹],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; fin_cases i <;> simp [hx],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; fin_cases i <;> simp [hx]⟩

@[scoped simp] theorem coe_diagGL (x : K) (hx : x ≠ 0) :
    ((diagGL x hx : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![(1 : K), x] := rfl

theorem coe_diagGL_pow (x : K) (hx : x ≠ 0) (n : ℕ) :
    ((diagGL x hx ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![(1 : K), x ^ n] := by
  rw [Units.val_pow_eq_pow_val, coe_diagGL, Matrix.diagonal_pow]
  congr 1
  ext i; fin_cases i <;> simp

end Generic

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (natGenerator_dvd_iff' v _).mp dvd_rfl

theorem natGenerator_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Rat.HeightOneSpectrum.natGenerator v = ℓ :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp
    ((natGenerator_dvd_iff' v ℓ).mpr hv)

noncomputable def placeOf (ℓ : ℕ) : HeightOneSpectrum (𝓞 ℚ) :=
  if h : ℓ.Prime then (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, h⟩
  else (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩

theorem natGenerator_placeOf {ℓ : ℕ} (hℓ : ℓ.Prime) : Rat.HeightOneSpectrum.natGenerator (placeOf ℓ) = ℓ := by
  rw [placeOf, dif_pos hℓ]
  exact congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨ℓ, hℓ⟩)

theorem natCast_mem_placeOf {ℓ : ℕ} (hℓ : ℓ.Prime) : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (placeOf ℓ).asIdeal := by
  have := natGenerator_mem (placeOf ℓ)
  rwa [natGenerator_placeOf hℓ] at this

theorem eq_placeOf_iff {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v = placeOf ℓ ↔ Rat.HeightOneSpectrum.natGenerator v = ℓ := by
  constructor
  · rintro rfl; exact natGenerator_placeOf hℓ
  · intro h
    apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    rw [placeOf, dif_pos hℓ, Equiv.apply_symm_apply]
    exact Subtype.ext h

theorem placeOf_injective {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (h : placeOf ℓ = placeOf ℓ') : ℓ = ℓ' := by
  rw [← natGenerator_placeOf hℓ, ← natGenerator_placeOf hℓ', h]

theorem natCast_ne_zero_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  exact_mod_cast hn

theorem map_getD_range_length {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    rw [List.length_map, List.length_range] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

theorem prod_range_getD_eq_prod (l : List ℕ) :
    (∏ i ∈ Finset.range l.length, l.getD i 1) = l.prod := by
  conv_rhs => rw [← map_getD_range_length l 1]
  rw [← List.toFinset_range, List.prod_toFinset _ (List.nodup_range)]

theorem map_symm_mem_localBoxUnits {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (h₁ : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox Λ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (g : GL (Fin 2) (v.adicCompletion ℚ))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hgi : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ) :
    Units.map φ.symm.toRingHom.toMonoidHom g ∈ Submodule.localBoxUnits Λ v := by
  rw [Submodule.mem_localBoxUnits_iff, Units.coe_map, Units.coe_map_inv]
  refine ⟨(h₁ _).mpr ?_, (h₁ _).mpr ?_⟩
  · intro i j
    have e : φ (φ.symm.toRingHom.toMonoidHom (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := RingEquiv.apply_symm_apply φ _
    rw [e]; exact hg i j
  · intro i j
    have e : φ (φ.symm.toRingHom.toMonoidHom (((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))) =
        ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
      RingEquiv.apply_symm_apply φ _
    rw [e]; exact hgi i j

end QFactAsm
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq.QFactAsm"

open QFactAsm IsDedekindDomain NumberField in

theorem solution
    {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) :
    ∃ (k : ℕ) (rs : ℕ → ℕ) (ss : ℕ → (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      (∀ i < k, (rs i).Prime ∧ ss i ∈ primeHeckeSet Λ₁ (rs i)) ∧ (∏ i ∈ Finset.range k, rs i) = N ∧
        ∃ v ∈ Submodule.finiteIdeleStabilizer Λ₁, m = ((List.range k).map ss).prod * v := by
  classical
  obtain ⟨ha, hb⟩ := hΛ₁.ne_zero_and_ne_zero
  have hab : a ≠ 0 ∧ b ≠ 0 := ⟨ha, hb⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨hL2i, hL2ii⟩ :=
    hΛ₁.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq hab N m hm₁ hmN hRN

  choose φ hφ h₁ k₁ k₂ hk₁ hk₁i hk₂ hk₂i heq using
    fun (ℓ : ℕ) (hℓ : ℓ.Prime) (hd : ℓ ∣ N) => (hL2ii (placeOf ℓ) ℓ hℓ (natCast_mem_placeOf hℓ) hd).2

  let yloc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hd : ℓ ∣ N), (ℍ[ℚ, a, b] ⊗[ℚ] (placeOf ℓ).adicCompletion ℚ)ˣ :=
    fun ℓ hℓ hd => Units.map (φ ℓ hℓ hd).symm.toRingHom.toMonoidHom
      (k₁ ℓ hℓ hd * diagGL ((ℓ : ℕ) : (placeOf ℓ).adicCompletion ℚ)
        (natCast_ne_zero_adicCompletion _ hℓ.ne_zero) * (k₁ ℓ hℓ hd)⁻¹)

  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hd : ℓ ∣ N), ∃ t : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOf ℓ) (t : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        (yloc ℓ hℓ hd : ℍ[ℚ, a, b] ⊗[ℚ] (placeOf ℓ).adicCompletion ℚ) ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ placeOf ℓ →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (t : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    intro ℓ hℓ hd
    obtain ⟨β, hβ₁, hβ₂⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {placeOf ℓ}
      (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 ℚ) => (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)
        (placeOf ℓ) (yloc ℓ hℓ hd))
    refine ⟨β, ?_, fun w hw => hβ₂ w (by simpa using hw)⟩
    rw [hβ₁ _ (Finset.mem_singleton_self _), Pi.mulSingle_eq_same]
  choose t ht₁ ht₂ using hT

  let T : ℕ → (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := fun ℓ => if h : ℓ.Prime ∧ ℓ ∣ N then t ℓ h.1 h.2 else 1
  have hTeq : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hd : ℓ ∣ N), T ℓ = t ℓ hℓ hd := fun ℓ hℓ hd => dif_pos ⟨hℓ, hd⟩

  have hHecke : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hd : ℓ ∣ N), T ℓ ∈ primeHeckeSet Λ₁ ℓ := by
    intro ℓ hℓ hd
    rw [hTeq ℓ hℓ hd]
    refine QuaternionAlgebra.IsOrder.mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_conj_diagonal hab hΛ₁.isOrder
      (placeOf ℓ) hℓ (natCast_mem_placeOf hℓ) (φ ℓ hℓ hd) (hφ ℓ hℓ hd) (h₁ ℓ hℓ hd)
      (k₁ ℓ hℓ hd) (k₁ ℓ hℓ hd)⁻¹ (hk₁ ℓ hℓ hd) (hk₁i ℓ hℓ hd) (hk₁i ℓ hℓ hd) ?_ (t ℓ hℓ hd) ?_ (ht₂ ℓ hℓ hd)
    · intro i j; rw [inv_inv]; exact hk₁ ℓ hℓ hd i j
    · rw [ht₁ ℓ hℓ hd]
      rfl

  set P : List ℕ := N.primeFactorsList with hP
  have hPmem : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ∣ N := fun ℓ h =>
    ⟨Nat.prime_of_mem_primeFactorsList h, Nat.dvd_of_mem_primeFactorsList h⟩
  refine ⟨P.length, fun i => P.getD i 1, fun i => T (P.getD i 1), ?_, ?_, ?_⟩
  · intro i hi
    have hmem : P.getD i 1 ∈ P := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact ⟨(hPmem _ hmem).1, hHecke _ (hPmem _ hmem).1 (hPmem _ hmem).2⟩
  · rw [prod_range_getD_eq_prod]; exact Nat.prod_primeFactorsList hN0
  · have hPT : ((List.range P.length).map fun i => T (P.getD i 1)).prod = (P.map T).prod := by
      rw [show (fun i => T (P.getD i 1)) = T ∘ (fun i => P.getD i 1) from rfl, ← List.map_map,
        map_getD_range_length]
    rw [hPT]
    refine ⟨((P.map T).prod)⁻¹ * m, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      Λ₁ hΛ₁.isOrder]
    intro w
    rw [map_mul, map_inv]
    by_cases hw : ((N : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      obtain ⟨ℓ, hℓ, hd, rfl⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ w = placeOf ℓ :=
        ⟨_, Rat.HeightOneSpectrum.prime_natGenerator w, (natGenerator_dvd_iff' w N).mpr hw,
          (eq_placeOf_iff (Rat.HeightOneSpectrum.prime_natGenerator w) w).mpr rfl⟩
      have hstep : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOf ℓ)).toRingHom.toMonoidHom (T ℓ) =
          yloc ℓ hℓ hd := by
        rw [hTeq ℓ hℓ hd]; ext; exact ht₁ ℓ hℓ hd
      have hprod : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOf ℓ)).toRingHom.toMonoidHom (P.map T).prod =
          (yloc ℓ hℓ hd) ^ (padicValNat ℓ N) := by
        rw [ListProdEval.map_prod_map_eq_pow_count _ T ℓ P ?_, hstep, ← Nat.factorization_def N hℓ,
          ← Nat.primeFactorsList_count_eq]
        intro ℓ' hℓ'P hne
        obtain ⟨hℓ', hd'⟩ := hPmem ℓ' hℓ'P
        rw [hTeq ℓ' hℓ' hd']
        ext
        rw [Units.coe_map, Units.val_one]
        exact ht₂ ℓ' hℓ' hd' (placeOf ℓ) (fun h => hne (placeOf_injective hℓ' hℓ h.symm))
      have hm : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOf ℓ)).toRingHom.toMonoidHom m =
          Units.map (φ ℓ hℓ hd).symm.toRingHom.toMonoidHom
            (k₁ ℓ hℓ hd * diagGL ((ℓ : ℕ) : (placeOf ℓ).adicCompletion ℚ)
              (natCast_ne_zero_adicCompletion _ hℓ.ne_zero) ^ (padicValNat ℓ N) * k₂ ℓ hℓ hd) := by
        ext
        rw [Units.coe_map, Units.coe_map]
        apply (φ ℓ hℓ hd).injective
        change φ ℓ hℓ hd (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (placeOf ℓ) (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
          φ ℓ hℓ hd ((φ ℓ hℓ hd).symm _)
        rw [RingEquiv.apply_symm_apply, heq ℓ hℓ hd, Units.val_mul, Units.val_mul, coe_diagGL_pow]
      have hy : (yloc ℓ hℓ hd) ^ (padicValNat ℓ N) =
          Units.map (φ ℓ hℓ hd).symm.toRingHom.toMonoidHom
            (k₁ ℓ hℓ hd * diagGL ((ℓ : ℕ) : (placeOf ℓ).adicCompletion ℚ)
              (natCast_ne_zero_adicCompletion _ hℓ.ne_zero) ^ (padicValNat ℓ N) * (k₁ ℓ hℓ hd)⁻¹) := by
        simp only [yloc]
        rw [← map_pow, conj_pow]
      rw [hprod, hm, hy, ← map_inv, ← map_mul]
      have hgrp : (k₁ ℓ hℓ hd * diagGL ((ℓ : ℕ) : (placeOf ℓ).adicCompletion ℚ)
              (natCast_ne_zero_adicCompletion _ hℓ.ne_zero) ^ (padicValNat ℓ N) * (k₁ ℓ hℓ hd)⁻¹)⁻¹ *
            (k₁ ℓ hℓ hd * diagGL ((ℓ : ℕ) : (placeOf ℓ).adicCompletion ℚ)
              (natCast_ne_zero_adicCompletion _ hℓ.ne_zero) ^ (padicValNat ℓ N) * k₂ ℓ hℓ hd) =
            k₁ ℓ hℓ hd * k₂ ℓ hℓ hd := by
        group
      rw [hgrp]
      refine map_symm_mem_localBoxUnits Λ₁ (placeOf ℓ) (φ ℓ hℓ hd) (h₁ ℓ hℓ hd) _ ?_ ?_
      · rw [Units.val_mul]; exact IsInt.mul _ (hk₁ ℓ hℓ hd) (hk₂ ℓ hℓ hd)
      · rw [mul_inv_rev, Units.val_mul]; exact IsInt.mul _ (hk₂i ℓ hℓ hd) (hk₁i ℓ hℓ hd)
    ·
      have hprod : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom (P.map T).prod = 1 := by
        refine ListProdEval.map_prod_map_eq_one _ T P (fun ℓ' hℓ'P => ?_)
        obtain ⟨hℓ', hd'⟩ := hPmem ℓ' hℓ'P
        rw [hTeq ℓ' hℓ' hd']
        ext
        rw [Units.coe_map, Units.val_one]
        refine ht₂ ℓ' hℓ' hd' w (fun h => hw ?_)
        rw [← natGenerator_dvd_iff', h, natGenerator_placeOf hℓ']
        exact hd'
      rw [hprod, inv_one, one_mul]
      exact hL2i w hw

end S_QuaternionAlgebra_exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq
end P2MW
export P2MW.S_QuaternionAlgebra_exists_primeHeckeSet_list_prod_mul_eq_of_mem_finiteAdeleBox_of_relIndex_inf_conjByFiniteIdele_eq (solution)
