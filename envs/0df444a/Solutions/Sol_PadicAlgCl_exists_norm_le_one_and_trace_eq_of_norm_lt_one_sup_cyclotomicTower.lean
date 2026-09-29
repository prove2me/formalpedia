-- Prove2me | solution 1 for PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6f7a8288-f844-59aa-9343-db41011f0a2b

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
import Theorems.Thm_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower

set_option autoImplicit false

noncomputable section

namespace TP9

open Polynomial IntermediateField

section BaseChange

variable {k : Type*} {Ω' : Type*} [Field k] [Field Ω'] [Algebra k Ω']

lemma adjoin_simple_subset {F F' : IntermediateField k Ω'} (h : F ≤ F') (α : Ω') :
    ((IntermediateField.adjoin F {α} : IntermediateField F Ω') : Set Ω') ⊆
      ((IntermediateField.adjoin F' {α} : IntermediateField F' Ω') : Set Ω') := by
  intro z hz
  have hz' : z ∈ (IntermediateField.adjoin F {α}).toSubfield := hz
  rw [IntermediateField.adjoin_toSubfield] at hz'
  change z ∈ (IntermediateField.adjoin F' {α}).toSubfield
  rw [IntermediateField.adjoin_toSubfield]
  refine Subfield.closure_mono ?_ hz'
  apply Set.union_subset_union_left
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, h c.2⟩, rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem coe_trace_adjoin_simple_eq {F F' : IntermediateField k Ω'} (hFF' : F ≤ F') {α : Ω'}
    (hα : IsIntegral F α) (hα' : IsIntegral F' α)
    (hdeg : (minpoly F' α).natDegree = (minpoly F α).natDegree)
    {y : Ω'} (hy : y ∈ IntermediateField.adjoin F {α})
    (hy' : y ∈ IntermediateField.adjoin F' {α}) :
    ((Algebra.trace F' (IntermediateField.adjoin F' {α}) ⟨y, hy'⟩ : F') : Ω') =
      ((Algebra.trace F (IntermediateField.adjoin F {α}) ⟨y, hy⟩ : F) : Ω') := by
  classical
  set E : IntermediateField F Ω' := IntermediateField.adjoin F {α} with hEdef
  set E' : IntermediateField F' Ω' := IntermediateField.adjoin F' {α} with hE'def

  let ι : E →+* E' :=
    { toFun := fun z => ⟨z.1, adjoin_simple_subset hFF' α z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let j : F →+* F' :=
    { toFun := fun c => ⟨c.1, hFF' c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιcoe : ∀ z : E, ((ι z : E') : Ω') = (z : Ω') := fun _ => rfl
  have hjcoe : ∀ c : F, ((j c : F') : Ω') = (c : Ω') := fun _ => rfl

  let pb : PowerBasis F E := IntermediateField.adjoin.powerBasis hα
  let pb' : PowerBasis F' E' := IntermediateField.adjoin.powerBasis hα'
  have hd : pb.dim = pb'.dim := by
    change (minpoly F α).natDegree = (minpoly F' α).natDegree
    exact hdeg.symm
  let e : Fin pb.dim ≃ Fin pb'.dim := finCongr hd
  have hb : ∀ i : Fin pb.dim, ι (pb.basis i) = pb'.basis (e i) := by
    intro i
    apply Subtype.ext
    rw [hιcoe, PowerBasis.coe_basis, PowerBasis.coe_basis]
    simp only [finCongr_apply, Fin.val_cast, e, pb, pb', IntermediateField.adjoin.powerBasis_gen]
    rw [IntermediateField.coe_pow, IntermediateField.coe_pow, IntermediateField.AdjoinSimple.coe_gen,
      IntermediateField.AdjoinSimple.coe_gen]
  have hsmul : ∀ (c : F) (z : E), ι (c • z) = j c • ι z := by
    intro c z
    apply Subtype.ext
    rw [hιcoe, IntermediateField.coe_smul, IntermediateField.coe_smul]
    rfl

  have hrepr : ∀ (z : E) (i : Fin pb.dim), pb'.basis.repr (ι z) (e i) = j (pb.basis.repr z i) := by
    intro z i
    have hz : z = ∑ i, pb.basis.repr z i • pb.basis i := (pb.basis.sum_repr z).symm
    have hιz : ι z = ∑ i' : Fin pb'.dim, (fun i' => j (pb.basis.repr z (e.symm i'))) i' • pb'.basis i' := by
      conv_lhs => rw [hz]
      have hms := map_sum ι.toAddMonoidHom (fun i => pb.basis.repr z i • pb.basis i) Finset.univ
      rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at hms
      rw [hms]
      refine Fintype.sum_equiv e _ _ fun i => ?_
      simp only [hsmul, hb, Equiv.symm_apply_apply]
    rw [hιz, ← pb'.basis.equivFun_symm_apply, ← pb'.basis.equivFun_apply,
      LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]

  have hy_eq : (⟨y, hy'⟩ : E') = ι ⟨y, hy⟩ := rfl
  rw [hy_eq, Algebra.trace_eq_matrix_trace pb.basis, Algebra.trace_eq_matrix_trace pb'.basis,
    Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [show (∑ i' : Fin pb'.dim, pb'.basis.repr (ι ⟨y, hy⟩ * pb'.basis i') i') =
      ∑ i : Fin pb.dim, pb'.basis.repr (ι ⟨y, hy⟩ * pb'.basis (e i)) (e i) from
    (Fintype.sum_equiv e _ _ fun i => rfl).symm]
  rw [IntermediateField.coe_sum, IntermediateField.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hb, ← map_mul, hrepr, hjcoe]

end BaseChange

section Engine

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma exists_monic_map_eq {k : Type*} [Field k] [Algebra k Ω] (F : IntermediateField k Ω)
    {f : Polynomial Ω} (hf : f.Monic) (hcoeff : ∀ i, f.coeff i ∈ F) :
    ∃ g : F[X], g.map (algebraMap F Ω) = f ∧ g.natDegree = f.natDegree ∧ g.Monic := by
  refine Polynomial.lifts_and_natDegree_eq_and_monic ?_ hf
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro i
  exact ⟨⟨f.coeff i, hcoeff i⟩, rfl⟩

theorem engine (Kinf : IntermediateField ℚ_[p] Ω) (F : ℕ → IntermediateField ℚ_[p] Ω)
    (hmono : Monotone F) (hsup : Kinf = ⨆ n, F n) [hfd : ∀ n, FiniteDimensional ℚ_[p] (F n)]
    (HW : ∀ (M : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] M] (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ z : extendScalars (F := F n) (E := M ⊔ F n) le_sup_right,
          (∀ w : extendScalars (F := F n) (E := M ⊔ F n) le_sup_right,
            ‖(w : Ω)‖ ≤ 1 →
            ‖((Algebra.trace ↥(F n) ↥(extendScalars (F := F n) (E := M ⊔ F n) le_sup_right)
              (z * w) : ↥(F n)) : Ω)‖ ≤ 1) →
          ‖(z : Ω)‖ ≤ (p : ℝ) ^ ε)
    (L : IntermediateField Kinf Ω) [FiniteDimensional Kinf L]
    (x : Kinf) (hx : ‖(x : Ω)‖ < 1) :
    ∃ y : L, ‖(y : Ω)‖ ≤ 1 ∧ Algebra.trace Kinf L y = x := by
  classical

  have hle : ∀ n, F n ≤ Kinf := fun n => hsup ▸ le_iSup F n
  have hmem : ∀ z : Ω, z ∈ Kinf → ∃ n, z ∈ F n := by
    intro z hz
    rw [hsup] at hz
    have hz' : z ∈ ((⨆ n, F n : IntermediateField ℚ_[p] Ω) : Set Ω) := hz
    rw [coe_iSup_of_directed hmono.directed_le, Set.mem_iUnion] at hz'
    exact hz'

  by_cases hx0 : x = 0
  · exact ⟨0, by simp, by rw [map_zero, hx0]⟩
  have hx0' : (x : Ω) ≠ 0 := by simpa using hx0
  have hxpos : 0 < ‖(x : Ω)‖ := norm_pos_iff.mpr hx0'
  set ε : ℝ := -Real.logb p ‖(x : Ω)‖ with hεdef
  have hε : 0 < ε := by
    rw [hεdef, neg_pos]
    exact Real.logb_neg (one_lt_p p) hxpos hx
  have hpε : ((p : ℝ) ^ ε)⁻¹ = ‖(x : Ω)‖ := by
    rw [hεdef, Real.rpow_neg (p_pos p).le, inv_inv,
      Real.rpow_logb (p_pos p) (one_lt_p p).ne' hxpos]

  obtain ⟨α, hprim⟩ := Field.exists_primitive_element Kinf L
  have hαint : IsIntegral Kinf α := Algebra.IsIntegral.isIntegral α
  set a : Ω := (α : Ω) with hadef
  set f : Kinf[X] := minpoly Kinf α with hfdef
  have hfa : minpoly Kinf a = f := by
    rw [hadef, show (α : Ω) = L.val α from rfl, minpoly.algHom_eq L.val L.val.injective]
  have hfmonic : f.Monic := minpoly.monic hαint
  set fΩ : Polynomial Ω := f.map (algebraMap Kinf Ω) with hfΩdef
  have hfΩmonic : fΩ.Monic := hfmonic.map _
  have hfΩdeg : fΩ.natDegree = f.natDegree := (Polynomial.natDegree_map_eq_of_injective
    (algebraMap Kinf Ω).injective f)
  have hfΩa : fΩ.eval a = 0 := by
    rw [hfΩdef, eval_map_algebraMap, hadef, show (α : Ω) = L.val α from rfl, aeval_algHom_apply,
      hfdef, minpoly.aeval, map_zero]

  have hcoef : ∀ i, ∃ m, ((f.coeff i : Kinf) : Ω) ∈ F m := fun i => hmem _ (f.coeff i).2
  choose m hm using hcoef
  obtain ⟨n₁, hn₁⟩ := hmem (x : Ω) x.2
  set n₀ : ℕ := f.support.sup m with hn₀def
  have hcoefF : ∀ n, n₀ ≤ n → ∀ i, fΩ.coeff i ∈ F n := by
    intro n hn i
    rw [hfΩdef, coeff_map]
    by_cases hi : i ∈ f.support
    · exact hmono ((Finset.le_sup hi).trans hn) (hm i)
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
      exact zero_mem _

  set M : IntermediateField ℚ_[p] Ω := IntermediateField.adjoin ℚ_[p] {a} with hMdef
  haveI : FiniteDimensional ℚ_[p] M :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  obtain ⟨N, hN⟩ := HW M ε hε
  set n : ℕ := max N (max n₀ n₁) with hndef
  have hnN : N ≤ n := le_max_left _ _
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hn₁' : n₁ ≤ n := (le_max_right _ _).trans (le_max_right _ _)

  obtain ⟨g, hgmap, hgdeg, hgmonic⟩ := exists_monic_map_eq p (F n) hfΩmonic (hcoefF n hn₀)
  have hga : aeval a g = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hgmap, hfΩa]
  have hαFn : IsIntegral (F n) a := ⟨g, hgmonic, by rw [← aeval_def, hga]⟩
  have hdeg : (minpoly Kinf a).natDegree = (minpoly (F n) a).natDegree := by
    apply le_antisymm
    ·
      set h := minpoly (F n) a with hhdef
      have hhmonic : h.Monic := minpoly.monic hαFn
      obtain ⟨h', hh'map, hh'deg, hh'monic⟩ := exists_monic_map_eq p Kinf (hhmonic.map
        (algebraMap (F n) Ω)) (fun i => by rw [coeff_map]; exact hle n (h.coeff i).2)
      have hh'a : aeval a h' = 0 := by
        rw [aeval_def, eval₂_eq_eval_map, hh'map, eval_map_algebraMap, hhdef, minpoly.aeval]
      calc (minpoly Kinf a).natDegree ≤ h'.natDegree :=
            natDegree_le_of_dvd (minpoly.dvd Kinf a hh'a) hh'monic.ne_zero
        _ = h.natDegree := by
            rw [hh'deg, natDegree_map_eq_of_injective (algebraMap (F n) Ω).injective]
    · calc (minpoly (F n) a).natDegree ≤ g.natDegree :=
            natDegree_le_of_dvd (minpoly.dvd (F n) a hga) hgmonic.ne_zero
        _ = (minpoly Kinf a).natDegree := by rw [hgdeg, hfΩdeg, hfa]

  set En : IntermediateField (F n) Ω := extendScalars (F := F n) (E := M ⊔ F n) le_sup_right
    with hEndef
  have hEn : En = IntermediateField.adjoin (F n) {a} := by
    apply IntermediateField.restrictScalars_injective ℚ_[p]
    rw [hEndef, extendScalars_restrictScalars, restrictScalars_adjoin, adjoin_union, adjoin_self,
      sup_comm]
  haveI hEnfd : FiniteDimensional (F n) En := by
    rw [hEn]
    exact IntermediateField.adjoin.finiteDimensional hαFn

  have hcodiff := hN n hnN
  set xn : F n := ⟨(x : Ω), hmono hn₁' hn₁⟩ with hxndef
  have hxn : ‖(xn : Ω)‖ ≤ ((p : ℝ) ^ ε)⁻¹ := by
    rw [hpε]
  obtain ⟨y, hy1, hy2⟩ :=
    PadicAlgCl.exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le p (F n) En
      ((p : ℝ) ^ ε) hcodiff xn hxn

  have hyad : (y : Ω) ∈ IntermediateField.adjoin (F n) {a} := hEn ▸ y.2
  have htr1 : ((Algebra.trace (F n) (IntermediateField.adjoin (F n) {a}) ⟨y, hyad⟩ : F n) : Ω) =
      (x : Ω) := by
    have h1 : IntermediateField.equivOfEq hEn y = ⟨y, hyad⟩ := Subtype.ext rfl
    rw [← h1, Algebra.trace_eq_of_algEquiv, hy2]
  have hyK : (y : Ω) ∈ IntermediateField.adjoin Kinf {a} := adjoin_simple_subset (hle n) a hyad
  have hαK : IsIntegral Kinf a := Algebra.IsIntegral.isIntegral a
  have htr2 : ((Algebra.trace Kinf (IntermediateField.adjoin Kinf {a}) ⟨y, hyK⟩ : Kinf) : Ω) =
      (x : Ω) := by
    rw [coe_trace_adjoin_simple_eq (hle n) hαFn hαK hdeg hyad hyK, htr1]
  have hL : L = IntermediateField.adjoin Kinf {a} := by
    calc L = L.val.fieldRange := (fieldRange_val L).symm
      _ = IntermediateField.map L.val ⊤ := AlgHom.fieldRange_eq_map _
      _ = IntermediateField.map L.val Kinf⟮α⟯ := by rw [hprim]
      _ = IntermediateField.adjoin Kinf (L.val '' {α}) := adjoin_map _ _ _
      _ = IntermediateField.adjoin Kinf {a} := by rw [Set.image_singleton]; rfl
  have hyL : (y : Ω) ∈ L := by
    rw [hL]
    exact hyK
  refine ⟨⟨y, hyL⟩, hy1, ?_⟩
  apply Subtype.ext
  have h2 : IntermediateField.equivOfEq hL ⟨(y : Ω), hyL⟩ = ⟨y, hyK⟩ := Subtype.ext rfl
  rw [← htr2, ← h2, Algebra.trace_eq_of_algEquiv]

end Engine

section Cyclotomic

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Q" => PadicAlgCl.cyclotomicTower p

private lemma _root_.TP9.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "TP9" "exists_isPrimitiveRoot"
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    Q n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

scoped instance finiteDimensional_cyclotomicTower (n : ℕ) : FiniteDimensional ℚ_[p] (Q n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n
  rw [cyclotomicTower_eq_adjoin p n hζ]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)

end Cyclotomic

end TP9
p2m_reactivate "P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower.TP9"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower.TP9"

open TP9 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (L : IntermediateField ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) (PadicAlgCl p))
    [FiniteDimensional ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L]
    (x : ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n)) (hx : ‖(x : PadicAlgCl p)‖ < 1) :
    ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧
      Algebra.trace ↥(K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n) L y = x := by
  refine TP9.engine p (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n)
    (fun n => K ⊔ PadicAlgCl.cyclotomicTower p n) ?_ ?_ ?_ L x hx
  · exact fun m n hmn => sup_le_sup_left (PadicAlgCl.cyclotomicTower_mono p hmn) K
  · exact sup_iSup
  · intro M _ ε hε
    exact PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower p K M ε hε

end S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower (solution)
