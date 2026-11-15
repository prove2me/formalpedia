-- Prove2me | solution 1 for ResultantVNP.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T12:17:21.539971+00:00
-- url     : https://prove2.me/submissions/7edb9930-cce3-4557-98cc-3a2a2371fa1f

import Definitions.Def_ResultantVNP_quadRes
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_ge
import Theorems.Thm_MvResultant_blockDegree_le

set_option maxHeartbeats 400000

open MvPolynomial ResultantVNP Finset

namespace ResultantDegree

def coeffEquiv {n : ℕ} (d : Fin n → ℕ) :
    CoeffVar d ≃ HararySachs.Hyper.ResVar n d where
  toFun v := ⟨v.1, v.2.1, by simpa only [Finsupp.degree_eq_sum] using v.2.2⟩
  invFun v := ⟨v.1, v.2.1, by simpa only [Finsupp.degree_eq_sum] using v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma form_coeff {n : ℕ} (d : Fin n → ℕ)
    (F : Fin n → MvPolynomial (Fin n) ℂ) (hF : ∀ i, (F i).IsHomogeneous (d i))
    (i : Fin n) : form d (fun v => (F v.1).coeff v.2.1) i = F i := by
  classical
  ext e
  rw [form, coeff_sum]
  by_cases he : ∑ j, e j = d i
  · rw [sum_eq_single (⟨e,he⟩ : {e : Fin n →₀ ℕ // ∑ j, e j = d i})]
    · simp
    · intro v hv hne
      have hne' : v.1 ≠ e := fun heq => hne (Subtype.ext heq)
      simp [coeff_monomial,hne']
    · simp
  · rw [(hF i).coeff_eq_zero (by simpa only [Finsupp.degree_eq_sum] using he)]
    apply sum_eq_zero
    intro v hv
    have hne : v.1 ≠ e := by intro h; exact he (h ▸ v.2)
    simp [coeff_monomial,hne]

lemma compatible {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) :
    HararySachs.Hyper.IsResultant n d (rename (coeffEquiv d) (𝓡.res d)) := by
  classical
  obtain ⟨hz,hnorm,hirr⟩ := 𝓡.spec d hn hd
  refine ⟨?_,?_,?_⟩
  · intro F hF
    simp only [map_rename, aeval_def, Algebra.algebraMap_self, eval₂_id, eval_rename]
    convert (hz (fun v => (F v.1).coeff v.2.1)).symm using 1
    · simp_rw [form_coeff d F hF]
    · rfl
  · simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, eval_rename]
    exact hnorm
  · rw [map_rename]
    exact hirr.map (renameEquiv ℂ (coeffEquiv d)).toMulEquiv

lemma block {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) (i : Fin n) :
    (𝓡.res d).IsWeightedHomogeneous (fun v => if v.1 = i then 1 else 0)
      (∏ j ∈ univ.erase i, d j) := by
  classical
  let R := rename (coeffEquiv d) (𝓡.res d)
  have hR := compatible 𝓡 d hn hd
  obtain ⟨δ,hδ⟩ := MvResultant.isWeightedHomogeneous_block R hR i
  have hδeq : δ = ∏ j ∈ univ.erase i, d j :=
    le_antisymm (MvResultant.blockDegree_le hd R hR i δ hδ)
      (MvResultant.blockDegree_ge hd R hR i δ hδ)
  subst δ
  intro μ hμ
  have hc : coeff (μ.mapDomain (coeffEquiv d)) R ≠ 0 := by
    rwa [coeff_rename_mapDomain _ (coeffEquiv d).injective]
  have hw := hδ hc
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj (coeffEquiv d).injective] at hw
  exact hw

lemma scaling {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) (i : Fin n) (t : ℂ) (c : CoeffVar d → ℂ) :
    eval (fun v => if v.1 = i then t * c v else c v)
        (map (Int.castRingHom ℂ) (𝓡.res d)) =
      t ^ (∏ j ∈ univ.erase i, d j) * eval c (map (Int.castRingHom ℂ) (𝓡.res d)) := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res d)
  have hw : P.IsWeightedHomogeneous (fun v => if v.1 = i then 1 else 0)
      (∏ j ∈ univ.erase i, d j) := by
    intro μ hμ
    apply block 𝓡 d hn hd i
    intro hz
    apply hμ
    simp [P,coeff_map,hz]
  change eval _ P = _ * eval _ P
  simp only [eval_eq, mul_sum]
  apply sum_congr rfl
  intro μ hμ
  have hprod : ∏ v ∈ μ.support, (if v.1 = i then t * c v else c v) ^ μ v =
      t ^ (∏ j ∈ univ.erase i, d j) * ∏ v ∈ μ.support, c v ^ μ v := by
    calc
      _ = ∏ v ∈ μ.support, (t ^ (if v.1 = i then 1 else 0) * c v) ^ μ v := by
        apply prod_congr rfl
        intro v hv
        split_ifs <;> simp
      _ = (∏ v ∈ μ.support, t ^ (μ v * (if v.1 = i then 1 else 0))) *
          ∏ v ∈ μ.support, c v ^ μ v := by
        simp only [mul_pow,prod_mul_distrib,← pow_mul, Nat.mul_comm]
      _ = _ := by
        rw [prod_pow_eq_pow_sum]
        congr 2
        exact hw (mem_support_iff.mp hμ)
  rw [hprod]
  ring

lemma homogeneous {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) :
    (𝓡.res d).IsHomogeneous (∑ i, ∏ j ∈ univ.erase i, d j) := by
  classical
  intro μ hμ
  have hh : ∀ i : Fin n, Finsupp.weight (fun v : CoeffVar d =>
      if v.1 = i then 1 else 0) μ = ∏ j ∈ univ.erase i, d j :=
    fun i => block 𝓡 d hn hd i hμ
  calc
    _ = ∑ v, μ v := by simp [Finsupp.weight_eq_sum]
    _ = ∑ v : CoeffVar d, ∑ i : Fin n, μ v * (if v.1 = i then 1 else 0) := by simp
    _ = ∑ i : Fin n, ∑ v : CoeffVar d, μ v * (if v.1 = i then 1 else 0) := sum_comm
    _ = _ := sum_congr rfl fun i _ => by simpa only [Finsupp.weight_eq_sum,smul_eq_mul] using hh i

end ResultantDegree

theorem solution (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) :
    (∀ i : Fin n, MvPolynomial.IsWeightedHomogeneous
        (fun v : CoeffVar d => if v.1 = i then 1 else 0) (𝓡.res d)
        (∏ j ∈ Finset.univ.erase i, d j)) ∧
    (∀ (i : Fin n) (t : ℂ) (c : CoeffVar d → ℂ),
        MvPolynomial.eval (fun v => if v.1 = i then t * c v else c v)
            (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res d)) =
          t ^ (∏ j ∈ Finset.univ.erase i, d j) *
            MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res d))) ∧
    (𝓡.res d).IsHomogeneous (∑ i, ∏ j ∈ Finset.univ.erase i, d j) ∧
    (quadRes 𝓡 n).IsHomogeneous (n * 2 ^ (n - 1)) := by
  classical
  refine ⟨ResultantDegree.block 𝓡 d hn hd, ResultantDegree.scaling 𝓡 d hn hd,
    ResultantDegree.homogeneous 𝓡 d hn hd, ?_⟩
  have h := ResultantDegree.homogeneous 𝓡 (fun _ : Fin n => 2) hn (by omega)
  simpa [quadRes,prod_const,card_erase_of_mem (mem_univ _)] using h

#print axioms solution
