-- Prove2me | solution 1 for WeierstrassCurve.exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ab24b9bb-045a-5f73-b01b-aa2f7562a34c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two
import Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
import Theorems.Thm_Polynomial_separable_deuringPolynomial_map
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero

set_option autoImplicit false

open FormalGroup

namespace DerivAux

open WeierstrassCurve

theorem twoTorsionPolynomial_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    (W.map f).twoTorsionPolynomial = Cubic.map f W.twoTorsionPolynomial := by
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, map_mul, map_ofNat]

theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : ℕ) (W : WeierstrassCurve R) :
    (W.map f).hasseInvariant q = f (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  rw [twoTorsionPolynomial_map, Cubic.map_toPoly, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem legendreCurve_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) :
    (legendreCurve t).map f = legendreCurve (f t) := by
  simp only [legendreCurve, WeierstrassCurve.map, map_zero, map_neg, map_add, map_one]

theorem snd_hasseInvariant_eq_sum {k : Type} [Field k] (q : ℕ) (E₀ : WeierstrassCurve k) :
    ∃ c : Fin 5 → k, ∀ (K : Type) [CommRing K] [Algebra k K] (δ : Fin 5 → K)
      (E' : WeierstrassCurve (TrivSqZeroExt K K)),
      E'.a₁ = TrivSqZeroExt.inl (algebraMap k K E₀.a₁) + TrivSqZeroExt.inr (δ 0) →
      E'.a₂ = TrivSqZeroExt.inl (algebraMap k K E₀.a₂) + TrivSqZeroExt.inr (δ 1) →
      E'.a₃ = TrivSqZeroExt.inl (algebraMap k K E₀.a₃) + TrivSqZeroExt.inr (δ 2) →
      E'.a₄ = TrivSqZeroExt.inl (algebraMap k K E₀.a₄) + TrivSqZeroExt.inr (δ 3) →
      E'.a₆ = TrivSqZeroExt.inl (algebraMap k K E₀.a₆) + TrivSqZeroExt.inr (δ 4) →
        (E'.hasseInvariant q).snd = ∑ i, algebraMap k K (c i) * δ i := by
  classical
  let U := TrivSqZeroExt k (Fin 5 → k)
  let Eu : WeierstrassCurve U :=
    ⟨TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1),
     TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1),
     TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1),
     TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1),
     TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)⟩
  refine ⟨(Eu.hasseInvariant q).snd, ?_⟩
  intro K _ _ δ E' h1 h2 h3 h4 h6

  let L : (Fin 5 → k) →ₗ[k] K :=
    { toFun := fun m => ∑ i, algebraMap k K (m i) * δ i
      map_add' := fun m m' => by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, map_add, add_mul]
      map_smul' := fun r m => by
        rw [RingHom.id_apply, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc] }
  have hL : ∀ m, L m = ∑ i, algebraMap k K (m i) * δ i := fun m => rfl
  let g : (Fin 5 → k) →ₗ[k] TrivSqZeroExt K K := (TrivSqZeroExt.inrHom K K).restrictScalars k ∘ₗ L
  have hg : ∀ m, g m = TrivSqZeroExt.inr (L m) := fun m => rfl
  let Φ : U →ₐ[k] TrivSqZeroExt K K := TrivSqZeroExt.lift (Algebra.ofId k (TrivSqZeroExt K K)) g
    (fun x y => by rw [hg, hg, TrivSqZeroExt.inr_mul_inr])
    (fun r x => by
      rw [hg, hg, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl_mul_inr,
        Algebra.smul_def, smul_eq_mul])
    (fun r x => by
      rw [hg, hg, op_smul_eq_smul, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.inr_mul_inl, op_smul_eq_smul, Algebra.smul_def, smul_eq_mul])
  have hΦ : ∀ (a : k) (m : Fin 5 → k), Φ (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inl (algebraMap k K a) + TrivSqZeroExt.inr (L m) := by
    intro a m
    rw [map_add, TrivSqZeroExt.lift_apply_inl, TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply,
      TrivSqZeroExt.algebraMap_eq_inl', hg]
  have hLs : ∀ i : Fin 5, L (Pi.single i 1) = δ i := by
    intro i
    rw [hL, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hmap : Eu.map Φ.toRingHom = E' := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show Φ (TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1)) = E'.a₁
      rw [hΦ, hLs, h1]
    · show Φ (TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1)) = E'.a₂
      rw [hΦ, hLs, h2]
    · show Φ (TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1)) = E'.a₃
      rw [hΦ, hLs, h3]
    · show Φ (TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1)) = E'.a₄
      rw [hΦ, hLs, h4]
    · show Φ (TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)) = E'.a₆
      rw [hΦ, hLs, h6]
  rw [← hmap, hasseInvariant_map]
  show (Φ (Eu.hasseInvariant q)).snd = _
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (Eu.hasseInvariant q)]
  rw [hΦ, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add, hL]

end DerivAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hH : E₀.hasseInvariant q = 0) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      TrivSqZeroExt.snd (E₁.hasseInvariant q) ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := DerivAux.snd_hasseInvariant_eq_sum q E₀
  have hqodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq

  suffices hex : ∃ i, c i ≠ 0 by
    obtain ⟨i, hi⟩ := hex
    let δ : Fin 5 → k := Pi.single i 1
    let E₁ : WeierstrassCurve (DualNumber k) :=
      ⟨TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (δ 0), TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (δ 1),
       TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (δ 2), TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (δ 3),
       TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (δ 4)⟩
    have hfstφ : ∀ a d : k, (TrivSqZeroExt.fstHom k k k).toRingHom (TrivSqZeroExt.inl a + TrivSqZeroExt.inr d) = a := by
      intro a d
      show TrivSqZeroExt.fst (TrivSqZeroExt.inl a + TrivSqZeroExt.inr d : TrivSqZeroExt k k) = a
      rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]
    refine ⟨E₁, ?_, ?_⟩
    · exact WeierstrassCurve.ext (hfstφ _ _) (hfstφ _ _) (hfstφ _ _) (hfstφ _ _) (hfstφ _ _)
    · have hid : ∀ a : k, algebraMap k k a = a := fun a => rfl
      have e := hc k δ E₁ (by rw [hid]) (by rw [hid]) (by rw [hid]) (by rw [hid]) (by rw [hid])
      rw [e, Finset.sum_eq_single i, hid]
      · show c i * (Pi.single i (1 : k) : Fin 5 → k) i ≠ 0
        rw [Pi.single_eq_same, mul_one]; exact hi
      · intro j _ hj
        show algebraMap k k (c j) * (Pi.single i (1 : k) : Fin 5 → k) j = 0
        rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h

  let K := AlgebraicClosure k
  haveI hKq : CharP K q := charP_of_injective_algebraMap (algebraMap k K).injective q
  have hprime : q.Prime := Fact.out
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K q 2).mp (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp this
    exact hq this
  have h4K : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2K h2K
  set E : WeierstrassCurve K := E₀.map (algebraMap k K) with hEdef
  have hHE : E.hasseInvariant q = 0 := by
    rw [hEdef, DerivAux.hasseInvariant_map, hH, map_zero]

  have ha : E.twoTorsionPolynomial.a ≠ 0 := h4K
  have hsplit : (E.twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits := by
    rw [Polynomial.map_id]; exact IsAlgClosed.splits _
  obtain ⟨e₁, e₂, e₃, he⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hmapid : Cubic.map (RingHom.id K) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases E.twoTorsionPolynomial; rfl
  rw [hmapid] at he
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₁) two_pos

  have h2top : IsUnit (2 : (⊤ : ValuationSubring K)) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨2⁻¹, ValuationSubring.mem_top _⟩, ?_⟩
    apply Subtype.ext
    show (2 : K) * 2⁻¹ = 1
    exact mul_inv_cancel₀ h2K
  obtain ⟨l, κ, -, -, -, -, hκu, -, -, -, hκE⟩ :=
    WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two (⊤ : ValuationSubring K) h2top E
      (ValuationSubring.mem_top _) he hw
  have hκE' : κ • E = WeierstrassCurve.legendreCurve (l : K) := by
    rw [hκE, DerivAux.legendreCurve_map]; rfl

  set Hq : Polynomial K := (Polynomial.deuringPolynomial q).map (Int.castRingHom K) with hHq
  have hroot : Hq.eval (l : K) = 0 := by
    have h1 := WeierstrassCurve.hasseInvariant_variableChange (q := q) E κ
    rw [hκE', hHE, mul_zero, WeierstrassCurve.hasseInvariant_legendreCurve hqodd] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr h4K))
    · exact h
  have hsep : Hq.Separable := Polynomial.separable_deuringPolynomial_map q
  have hder : (Polynomial.derivative Hq).eval (l : K) ≠ 0 := by
    have := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := (l : K))
      (by rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_id]; exact hroot)
    rwa [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at this

  let T := TrivSqZeroExt K K
  haveI : CharP T q := charP_of_injective_algebraMap (algebraMap K T).injective q
  set EL : WeierstrassCurve T := WeierstrassCurve.legendreCurve (algebraMap K T (l : K) + TrivSqZeroExt.inr 1) with hEL
  have hinl : ∀ x : K, algebraMap K T x = TrivSqZeroExt.inl x := fun x => congrFun (TrivSqZeroExt.algebraMap_eq_inl K K) x
  have hHqT : (Polynomial.deuringPolynomial q).map (Int.castRingHom T) = Hq.map (algebraMap K T) := by
    rw [hHq, Polynomial.map_map]; congr 1; all_goals exact RingHom.ext_int _ _
  have hevalT : ∀ P : Polynomial K, (P.map (algebraMap K T)).eval (algebraMap K T (l : K)) =
      algebraMap K T (P.eval (l : K)) := by
    intro P; rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hHEL : (EL.hasseInvariant q).snd = (-4 : K) ^ ((q - 1) / 2) * (Polynomial.derivative Hq).eval (l : K) := by
    rw [hEL, WeierstrassCurve.hasseInvariant_legendreCurve hqodd, hHqT,
      Polynomial.eval_add_of_sq_eq_zero _ _ _ (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]),
      Polynomial.derivative_map, hevalT, hevalT, hroot, map_zero, _root_.zero_add, hinl,
      TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one,
      show ((-4 : T)) ^ ((q - 1) / 2) = algebraMap K T ((-4 : K) ^ ((q - 1) / 2)) by rw [map_pow, map_neg, map_ofNat],
      hinl, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.snd_inr, smul_eq_mul]

  set κT : WeierstrassCurve.VariableChange T := κ.map (algebraMap K T) with hκT
  set E' : WeierstrassCurve T := κT⁻¹ • EL with hE'
  have hE'red : E'.map (TrivSqZeroExt.fstHom K K K).toRingHom = E := by
    rw [hE', ← WeierstrassCurve.map_variableChange,
      show (κT⁻¹).map (TrivSqZeroExt.fstHom K K K).toRingHom = (κT.map (TrivSqZeroExt.fstHom K K K).toRingHom)⁻¹ from
        map_inv (WeierstrassCurve.VariableChange.mapHom (TrivSqZeroExt.fstHom K K K).toRingHom) κT,
      hκT, WeierstrassCurve.VariableChange.map_map,
      show (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K T) = RingHom.id K from
        RingHom.ext fun x => by
          show TrivSqZeroExt.fst (algebraMap K T x) = x
          rw [hinl]; exact TrivSqZeroExt.fst_inl K x,
      WeierstrassCurve.VariableChange.map_id, hEL, DerivAux.legendreCurve_map,
      show (TrivSqZeroExt.fstHom K K K).toRingHom (algebraMap K T (l : K) + TrivSqZeroExt.inr 1) = (l : K) by
        show TrivSqZeroExt.fst (algebraMap K T (l : K) + TrivSqZeroExt.inr (1 : K)) = (l : K)
        rw [hinl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero],
      ← hκE', inv_smul_smul]
  have hHE' : (E'.hasseInvariant q).snd ≠ 0 := by
    rw [hE', WeierstrassCurve.hasseInvariant_variableChange, show (κT⁻¹).u = κT.u⁻¹ from rfl, inv_inv, hκT,
      WeierstrassCurve.VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe, ← map_pow, hinl,
      ← TrivSqZeroExt.inl_fst_add_inr_snd_eq (EL.hasseInvariant q), mul_add, TrivSqZeroExt.inl_mul_inl,
      TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add,
      hHEL, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr h4K)) hder)

  let δ' : Fin 5 → K := ![E'.a₁.snd, E'.a₂.snd, E'.a₃.snd, E'.a₄.snd, E'.a₆.snd]
  have hfst : E'.a₁.fst = algebraMap k K E₀.a₁ ∧ E'.a₂.fst = algebraMap k K E₀.a₂ ∧ E'.a₃.fst = algebraMap k K E₀.a₃ ∧
      E'.a₄.fst = algebraMap k K E₀.a₄ ∧ E'.a₆.fst = algebraMap k K E₀.a₆ := by
    have h := hE'red
    rw [hEdef] at h
    obtain ⟨h1, h2, h3, h4, h6⟩ := (WeierstrassCurve.ext_iff.mp h)
    exact ⟨h1, h2, h3, h4, h6⟩
  have hmk : ∀ (x : T) (a d : K), x.fst = a → x.snd = d → x = TrivSqZeroExt.inl a + TrivSqZeroExt.inr d := by
    intro x a d ha hd
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, ha, hd]
  have e := hc K δ' E'
    (hmk _ _ (δ' 0) hfst.1 rfl) (hmk _ _ (δ' 1) hfst.2.1 rfl) (hmk _ _ (δ' 2) hfst.2.2.1 rfl)
    (hmk _ _ (δ' 3) hfst.2.2.2.1 rfl) (hmk _ _ (δ' 4) hfst.2.2.2.2 rfl)
  by_contra hall
  push_neg at hall
  apply hHE'
  rw [e]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hall i, map_zero, zero_mul]

end S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero (solution)
