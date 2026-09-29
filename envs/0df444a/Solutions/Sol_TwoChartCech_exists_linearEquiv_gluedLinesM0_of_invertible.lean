-- Prove2me | solution 1 for TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/72748c02-8996-5629-89e2-54d506854bd3

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import Theorems.Thm_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "TwoChartCech P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible.TwoChartCech LaurentPolynomial TensorProduct"

universe u

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart mem_invPolyPart_iff gluedLinesOverlap gluedLinesCover gluedLinesM0"
namespace ModelPicAux
p2m_open "TwoChartCech"

variable {k : Type u} [Field k] {s : ℕ}

theorem T_eq_single (j : ℤ) : (T j : k[T;T⁻¹]) = AddMonoidAlgebra.single j 1 := rfl

theorem support_mul_T (f : k[T;T⁻¹]) (j : ℤ) :
    (f * T j).coeff.support = f.coeff.support.map (addRightEmbedding j) := by
  rw [T_eq_single]
  exact AddMonoidAlgebra.support_coeff_mul_single f (1 : k) (fun y => by simp) j

theorem mul_T_mem_invPolyPart_iff (f : k[T;T⁻¹]) (j : ℤ) :
    f * T j ∈ invPolyPart k ↔ ∀ n ∈ f.coeff.support, n + j ≤ 0 := by
  rw [mem_invPolyPart_iff, support_mul_T]
  constructor
  · intro h n hn
    exact h (n + j) (Finset.mem_map_of_mem _ hn)
  · intro h n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    exact h m hm

theorem toLaurent_mem_polyPart (p : Polynomial k) : Polynomial.toLaurent p ∈ polyPart k := by
  intro n hn
  rw [LaurentPolynomial.support_coeff_toLaurent] at hn
  obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hn
  exact Int.natCast_nonneg m

theorem toLaurent_trunc_apply (f : k[T;T⁻¹]) (n : ℤ) :
    (Polynomial.toLaurent (LaurentPolynomial.trunc f)).coeff n = if 0 ≤ n then f.coeff n else 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    change (Polynomial.toLaurent (LaurentPolynomial.trunc p)).coeff n + (Polynomial.toLaurent (LaurentPolynomial.trunc q)).coeff n = _
    rw [hp, hq]
    split_ifs
    · rfl
    · exact add_zero 0
  | C_mul_T m r =>
    rw [LaurentPolynomial.trunc_C_mul_T]
    have hcoef : ∀ j : ℤ, (LaurentPolynomial.C r * T m : k[T;T⁻¹]).coeff j = if m = j then r else 0 := fun j => by
      rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]; exact Finsupp.single_apply
    split_ifs with hm hn hn
    · rw [Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hm, hcoef]
    · rw [Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hm, hcoef, if_neg]
      rintro rfl; exact hn hm
    · rw [map_zero, hcoef, if_neg]
      · rfl
      · rintro rfl; exact hm hn
    · rw [map_zero]; rfl

theorem toLaurent_trunc_of_mem_polyPart {f : k[T;T⁻¹]} (hf : f ∈ polyPart k) :
    Polynomial.toLaurent (LaurentPolynomial.trunc f) = f := by
  apply LaurentPolynomial.ext
  intro n
  rw [toLaurent_trunc_apply]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (hf n (Finsupp.mem_support_iff.mpr hne))

theorem toLaurent_mul_T_mem_invPolyPart_iff_degree_lt (p : Polynomial k) (d : ℕ) :
    Polynomial.toLaurent p * T (-((d : ℤ) - 1)) ∈ invPolyPart k ↔ p.degree < d := by
  rw [mul_T_mem_invPolyPart_iff, Polynomial.degree_lt_iff_coeff_zero]
  constructor
  · intro h m hm
    by_contra hne
    have hmem : (m : ℤ) ∈ (Polynomial.toLaurent p).coeff.support := by
      rw [LaurentPolynomial.support_coeff_toLaurent]
      exact Finset.mem_map.mpr ⟨m, Polynomial.mem_support_iff.mpr hne, rfl⟩
    have hle := h _ hmem
    omega
  · intro h n hn
    rw [LaurentPolynomial.support_coeff_toLaurent] at hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    have hlt : m < d := lt_of_not_ge fun hge => (Polynomial.mem_support_iff.mp hm) (h m hge)
    change (m : ℤ) + -((d : ℤ) - 1) ≤ 0
    omega

theorem eval_toLaurent (u : kˣ) (p : Polynomial k) : levalUnit k u (Polynomial.toLaurent p) = p.eval (u : k) := by
  rw [levalUnit, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id]

theorem eval_C (u : kˣ) (c : k) : levalUnit k u (LaurentPolynomial.C c) = c := by
  simp [LaurentPolynomial.eval₂_C]

theorem C_mem_polyPart (c : k) : (LaurentPolynomial.C c : k[T;T⁻¹]) ∈ polyPart k := by
  intro n hn
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single] at hn
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem C_mem_invPolyPart (c : k) : (LaurentPolynomial.C c : k[T;T⁻¹]) ∈ invPolyPart k := by
  intro n hn
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single] at hn
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem eq_C_of_mem_polyPart_of_mem_invPolyPart {f : k[T;T⁻¹]} (h0 : f ∈ polyPart k) (h1 : f ∈ invPolyPart k) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  apply LaurentPolynomial.ext
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hn)]
    by_contra hne
    have hmem : n ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hne
    exact hn (le_antisymm (h1 n hmem) (h0 n hmem))

variable (a b : Fin s → kˣ)

abbrev Req : Subalgebra k (Polynomial k × Polynomial k) :=
  AlgHom.equalizer
    (Pi.algHom k (fun _ : Fin s => k) fun i => (Polynomial.aeval ((a i : kˣ) : k)).comp (AlgHom.fst k (Polynomial k) (Polynomial k)))
    (Pi.algHom k (fun _ : Fin s => k) fun i => (Polynomial.aeval ((b i : kˣ) : k)).comp (AlgHom.snd k (Polynomial k) (Polynomial k)))

theorem mem_Req_iff (p : Polynomial k × Polynomial k) :
    p ∈ Req a b ↔ ∀ i, p.1.eval (a i : k) = p.2.eval (b i : k) := by
  rw [AlgHom.mem_equalizer]
  constructor
  · intro h i
    have := congrFun h i
    change Polynomial.aeval (a i : k) p.1 = Polynomial.aeval (b i : k) p.2 at this
    rwa [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval] at this
  · intro h
    funext i
    change Polynomial.aeval (a i : k) p.1 = Polynomial.aeval (b i : k) p.2
    rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval]
    exact h i

private abbrev _root_.TwoChartCech.ModelPicAux.A0 : Subalgebra k (k[T;T⁻¹] × k[T;T⁻¹]) := gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)

p2m_export "TwoChartCech.ModelPicAux" "A0"

def toA0 : ↥(Req a b) →ₐ[k] ↥(A0 a b) :=
  AlgHom.codRestrict
    (((Polynomial.toLaurentAlg.comp (AlgHom.fst k _ _)).prod (Polynomial.toLaurentAlg.comp (AlgHom.snd k _ _))).comp
      (Req a b).val)
    (A0 a b)
    (by
      intro p
      refine ⟨fun i => ?_, Subalgebra.mem_prod.2 ⟨toLaurent_mem_polyPart _, toLaurent_mem_polyPart _⟩⟩
      show levalUnit k (a i) (Polynomial.toLaurent p.1.1) = levalUnit k (b i) (Polynomial.toLaurent p.1.2)
      rw [eval_toLaurent, eval_toLaurent]
      exact (mem_Req_iff a b p.1).1 p.2 i)

theorem toA0_apply_coe (p : ↥(Req a b)) :
    ((toA0 a b p : ↥(A0 a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = (Polynomial.toLaurent p.1.1, Polynomial.toLaurent p.1.2) := rfl

theorem toA0_bijective : Function.Bijective (toA0 a b) := by
  constructor
  · intro p q h
    have h' : ((toA0 a b p : ↥(A0 a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = ((toA0 a b q : ↥(A0 a b)) : k[T;T⁻¹] × k[T;T⁻¹]) :=
      congrArg Subtype.val h
    rw [toA0_apply_coe, toA0_apply_coe, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (Polynomial.toLaurent_injective h'.1) (Polynomial.toLaurent_injective h'.2))
  · intro f
    obtain ⟨hnode, hpoly⟩ := f.2
    obtain ⟨h1, h2⟩ := Subalgebra.mem_prod.1 hpoly
    refine ⟨⟨(LaurentPolynomial.trunc f.1.1, LaurentPolynomial.trunc f.1.2), (mem_Req_iff a b _).2 fun i => ?_⟩, ?_⟩
    · have := hnode i
      rw [← toLaurent_trunc_of_mem_polyPart h1, ← toLaurent_trunc_of_mem_polyPart h2, eval_toLaurent, eval_toLaurent] at this
      exact this
    · apply Subtype.ext
      rw [toA0_apply_coe]
      exact Prod.ext (toLaurent_trunc_of_mem_polyPart h1) (toLaurent_trunc_of_mem_polyPart h2)

noncomputable def θ : ↥(Req a b) ≃ₐ[k] ↥(A0 a b) := AlgEquiv.ofBijective (toA0 a b) (toA0_bijective a b)

theorem θ_apply_coe (r : ↥(Req a b)) :
    ((θ a b r : ↥(A0 a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = (Polynomial.toLaurent r.1.1, Polynomial.toLaurent r.1.2) := by
  rw [θ, AlgEquiv.ofBijective_apply]; rfl

end TwoChartCech.ModelPicAux

end

open TwoChartCech.ModelPicAux

set_option maxHeartbeats 6400000 in
theorem solution (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (P : Type u) [AddCommGroup P] [Module (gluedLinesCover k a b).A0 P]
    [Module.Invertible (gluedLinesCover k a b).A0 P] :
    ∃ μ : Fin s → kˣ, Nonempty (P ≃ₗ[(gluedLinesCover k a b).A0] ↥(gluedLinesM0 k a b μ)) := by
  classical

  let R := ↥(Req a b)
  let θ' : R ≃ₐ[k] (gluedLinesCover k a b).A0 := θ a b

  letI algAR : Algebra (gluedLinesCover k a b).A0 R := (θ'.symm.toAlgHom.toRingHom).toAlgebra
  let Q := R ⊗[(gluedLinesCover k a b).A0] P
  haveI : Module.Invertible R Q := inferInstance

  obtain ⟨δ, hδsurj, -, hN⟩ :=
    CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const (fun i => (a i : k)) (fun i => (b i : k))
      (fun i j h => ha (Units.ext h)) (fun i j h => hb (Units.ext h))
  obtain ⟨w, hw⟩ := hδsurj (CommRing.Pic.mk R Q)
  obtain ⟨N, hNmem, ⟨eN⟩⟩ := hN w
  have e1 : Nonempty (Q ≃ₗ[R] (δ w : CommRing.Pic R)) := CommRing.Pic.mk_eq_iff.1 hw.symm
  obtain ⟨e1⟩ := e1
  let e2 : Q ≃ₗ[R] ↥N := e1.trans eN
  refine ⟨w, ⟨?_⟩⟩
  have hθ : ∀ r : R, ((θ' r : (gluedLinesCover k a b).A0) : k[T;T⁻¹] × k[T;T⁻¹]) =
      (Polynomial.toLaurent r.1.1, Polynomial.toLaurent r.1.2) := fun r => θ_apply_coe a b r
  have halg : ∀ x : (gluedLinesCover k a b).A0, algebraMap (gluedLinesCover k a b).A0 R x = θ'.symm x := by
    intro x; rw [RingHom.algebraMap_toAlgebra]; rfl

  let j : P →ₗ[(gluedLinesCover k a b).A0] Q := TensorProduct.mk (gluedLinesCover k a b).A0 R P 1
  have hj : ∀ p, j p = (1 : R) ⊗ₜ p := fun p => rfl
  have htmul : ∀ (r : R) (p : P), r ⊗ₜ[(gluedLinesCover k a b).A0] p = j (θ' r • p) := by
    intro r p
    rw [hj, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, halg, AlgEquiv.symm_apply_apply,
      mul_one]

  let B : R →ₗ[(gluedLinesCover k a b).A0] P →ₗ[(gluedLinesCover k a b).A0] P :=
    LinearMap.mk₂ (gluedLinesCover k a b).A0 (fun r p => θ' r • p)
      (fun r₁ r₂ p => by simp only [map_add, add_smul])
      (fun x r p => by
        show θ' (x • r) • p = x • θ' r • p
        rw [Algebra.smul_def, halg, map_mul, AlgEquiv.apply_symm_apply, mul_smul])
      (fun r p₁ p₂ => smul_add _ _ _)
      (fun x r p => smul_comm _ _ _)
  let ℓ : Q →ₗ[(gluedLinesCover k a b).A0] P := TensorProduct.lift B
  have hℓ : ∀ (r : R) (p : P), ℓ (r ⊗ₜ p) = θ' r • p := fun r p => TensorProduct.lift.tmul r p
  have hℓj : ∀ p, ℓ (j p) = p := fun p => by rw [hj, hℓ, map_one, one_smul]
  have hj_bij : Function.Bijective j := by
    constructor
    · intro p q h
      rw [← hℓj p, ← hℓj q, h]
    · intro q
      induction q using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul r p => exact ⟨θ' r • p, (htmul r p).symm⟩
      | add q₁ q₂ h₁ h₂ =>
          obtain ⟨p₁, rfl⟩ := h₁; obtain ⟨p₂, rfl⟩ := h₂
          exact ⟨p₁ + p₂, map_add _ _ _⟩

  have hmemN : ∀ n : ↥N, ∀ i, n.1.1.eval (a i : k) = (w i : k) * n.1.2.eval (b i : k) := fun n => (hNmem n.1).1 n.2
  let laurFun : ↥N → ↥(gluedLinesM0 k a b w) := fun n =>
    ⟨(Polynomial.toLaurent n.1.1, Polynomial.toLaurent n.1.2),
      ⟨fun i => by
        show levalUnit k (a i) (Polynomial.toLaurent n.1.1) = w i * levalUnit k (b i) (Polynomial.toLaurent n.1.2)
        rw [eval_toLaurent, eval_toLaurent]; exact hmemN n i,
       Subalgebra.mem_prod.2 ⟨toLaurent_mem_polyPart _, toLaurent_mem_polyPart _⟩⟩⟩
  have hlaur_coe : ∀ n : ↥N, ((laurFun n : ↥(gluedLinesM0 k a b w)) : k[T;T⁻¹] × k[T;T⁻¹]) =
      (Polynomial.toLaurent n.1.1, Polynomial.toLaurent n.1.2) := fun n => rfl
  have hlaur_add : ∀ n₁ n₂, laurFun (n₁ + n₂) = laurFun n₁ + laurFun n₂ := fun n₁ n₂ =>
    Subtype.ext (by
      show (laurFun (n₁ + n₂) : k[T;T⁻¹] × k[T;T⁻¹]) = (laurFun n₁ : k[T;T⁻¹] × k[T;T⁻¹]) + (laurFun n₂ : k[T;T⁻¹] × k[T;T⁻¹])
      rw [hlaur_coe, hlaur_coe, hlaur_coe]
      simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk])
  have hlaur_smul : ∀ (r : R) (n : ↥N), laurFun (r • n) = (θ' r) • laurFun n := fun r n =>
    Subtype.ext (by
      rw [hlaur_coe]
      show _ = ((θ' r : (gluedLinesCover k a b).A0) : k[T;T⁻¹] × k[T;T⁻¹]) * (laurFun n : k[T;T⁻¹] × k[T;T⁻¹])
      rw [hθ, hlaur_coe]
      show (Polynomial.toLaurent ((r : Polynomial k × Polynomial k) * (n : Polynomial k × Polynomial k)).1,
            Polynomial.toLaurent ((r : Polynomial k × Polynomial k) * (n : Polynomial k × Polynomial k)).2) = _
      simp [map_mul])
  have hlaur_bij : Function.Bijective laurFun := by
    constructor
    · intro n₁ n₂ h
      have h' := congrArg (fun z : ↥(gluedLinesM0 k a b w) => (z : k[T;T⁻¹] × k[T;T⁻¹])) h
      simp only [hlaur_coe, Prod.mk.injEq] at h'
      exact Subtype.ext (Prod.ext (Polynomial.toLaurent_injective h'.1) (Polynomial.toLaurent_injective h'.2))
    · intro m
      obtain ⟨hcond, hpoly⟩ := m.2
      obtain ⟨h1, h2⟩ := Subalgebra.mem_prod.1 hpoly
      refine ⟨⟨(LaurentPolynomial.trunc m.1.1, LaurentPolynomial.trunc m.1.2), (hNmem _).2 fun i => ?_⟩, ?_⟩
      · have := hcond i
        rw [← toLaurent_trunc_of_mem_polyPart h1, ← toLaurent_trunc_of_mem_polyPart h2, eval_toLaurent,
          eval_toLaurent] at this
        exact this
      · apply Subtype.ext
        rw [hlaur_coe]
        exact Prod.ext (toLaurent_trunc_of_mem_polyPart h1) (toLaurent_trunc_of_mem_polyPart h2)

  let F : P →ₗ[(gluedLinesCover k a b).A0] ↥(gluedLinesM0 k a b w) :=
    { toFun := fun p => laurFun (e2 (j p))
      map_add' := fun p q => by simp only [map_add, hlaur_add]
      map_smul' := fun x p => by
        rw [RingHom.id_apply, LinearMap.map_smul, ← algebraMap_smul R x (j p), LinearEquiv.map_smul, hlaur_smul,
          halg, AlgEquiv.apply_symm_apply] }
  exact LinearEquiv.ofBijective F
    ⟨hlaur_bij.1.comp (e2.injective.comp hj_bij.1), hlaur_bij.2.comp (e2.surjective.comp hj_bij.2)⟩

end S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible
end P2MW
export P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible (solution)
