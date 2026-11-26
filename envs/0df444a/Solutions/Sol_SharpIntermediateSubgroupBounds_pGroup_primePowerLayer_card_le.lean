-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.pGroup_primePowerLayer_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:42.265905+00:00
-- url     : https://prove2.me/submissions/98b82d57-fcc7-4280-929a-41950a8a8033

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_isCoatom_of_prime_index
import Theorems.Thm_SharpIntermediateSubgroupBounds_normal_of_index_eq_prime_of_isPGroup
import Theorems.Thm_SharpIntermediateSubgroupBounds_coatomFiber_card_le_relIndex
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerLayer_card_subgroup

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (T : Subgroup G) (hindex : T.index = p ^ a) (k : ℕ) :
    (primePowerLayer p k T ⊤).card ≤ qBinom p a k := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  induction a generalizing G T k with
  | zero =>
      have hT : T = ⊤ := Subgroup.index_eq_one.mp (by simpa using hindex)
      subst T
      cases k with
      | zero =>
          have hlayer : primePowerLayer p 0 (⊤ : Subgroup G) ⊤ = {⊤} := by
            ext Q
            constructor
            · intro hQ
              have hQl := mem_primePowerLayer.mp hQ
              exact Finset.mem_singleton.mpr
                (top_unique (Subgroup.relIndex_eq_one.mp (by simpa using hQl.2.2)))
            · intro hQ
              have hQtop := Finset.mem_singleton.mp hQ
              subst Q
              exact mem_primePowerLayer.mpr ⟨le_rfl, le_rfl, by simp⟩
          simp [hlayer]
      | succ k =>
          have hpow : p ^ (k + 1) ≠ 1 := by
            exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
          simp [primePowerLayer, hpow, hpow.symm]
  | succ a ih =>
      cases k with
      | zero =>
          have hlayer : primePowerLayer p 0 T ⊤ = {⊤} := by
            ext Q
            constructor
            · intro hQ
              have hQl := mem_primePowerLayer.mp hQ
              exact Finset.mem_singleton.mpr
                (top_unique (Subgroup.relIndex_eq_one.mp (by simpa using hQl.2.2)))
            · intro hQ
              have hQtop := Finset.mem_singleton.mp hQ
              subst Q
              exact mem_primePowerLayer.mpr ⟨le_top, le_rfl, by simp⟩
          simp [hlayer]
      | succ k =>
          obtain ⟨b, hTcard⟩ := (hG.to_subgroup T).exists_card_eq
          have hcardG : Nat.card G = p ^ (b + (a + 1)) := by
            rw [← T.card_mul_index, hTcard, hindex, ← pow_add]
          have hdvd : p ^ (b + a) ∣ Nat.card G := by
            rw [hcardG, show b + (a + 1) = (b + a) + 1 by omega, pow_succ]
            exact dvd_mul_right _ _
          obtain ⟨M, hMcard, hTM⟩ :=
            Sylow.exists_subgroup_card_pow_prime_le (G := G) p hdvd T hTcard (by omega)
          have hMindex : M.index = p := by
            apply Nat.mul_left_cancel (pow_pos hp.pos _)
            calc
              p ^ (b + a) * M.index = Nat.card G := by
                rw [← hMcard]
                exact M.card_mul_index
              _ = p ^ (b + a) * p := by
                rw [hcardG, show b + (a + 1) = (b + a) + 1 by omega, pow_succ]
          letI : M.Normal := normal_of_index_eq_prime_of_isPGroup hp hG M hMindex
          have hMcoatom : IsCoatom M := isCoatom_of_prime_index M (hMindex.symm ▸ hp)
          have hTrelM : T.relIndex M = p ^ a := by
            have htower := T.relIndex_mul_index hTM
            apply Nat.mul_right_cancel hp.pos
            simpa [hMindex, hindex, pow_succ] using htower
          let layer := primePowerLayer p (k + 1) T ⊤
          let inside := layer.filter fun Q ↦ Q ≤ M
          let outside := layer.filter fun Q ↦ ¬Q ≤ M
          have hsplit : inside.card + outside.card = layer.card := by
            exact Finset.card_filter_add_card_filter_not (s := layer) (fun Q ↦ Q ≤ M)
          let lowerLayer := primePowerLayer p k T M
          have hins_maps : (inside : Set (Subgroup G)) ⊆ (lowerLayer : Set (Subgroup G)) := by
            intro Q hQ
            have hQi := Finset.mem_filter.mp hQ
            have hQl := mem_primePowerLayer.mp hQi.1
            apply mem_primePowerLayer.mpr
            refine ⟨hQl.1, hQi.2, ?_⟩
            have htower := Q.relIndex_mul_index hQi.2
            apply Nat.mul_right_cancel hp.pos
            calc
              Q.relIndex M * p = Q.index := by
                rw [← hMindex]
                exact htower
              _ = p ^ (k + 1) := by
                rw [← Subgroup.relIndex_top_right]
                exact hQl.2.2
              _ = p ^ k * p := by rw [pow_succ]
          have hlower : lowerLayer.card ≤ qBinom p a k := by
            rw [primePowerLayer_card_subgroup hTM]
            exact ih (G := M) (hG.to_subgroup M) (T.subgroupOf M) (by
              simpa using
                (Subgroup.relIndex_subgroupOf (H := T) (K := M) (L := M) le_rfl).trans hTrelM) k
          have hinside : inside.card ≤ qBinom p a k :=
            (Finset.card_le_card hins_maps).trans hlower
          let upperLayer := primePowerLayer p (k + 1) T M
          have hout_maps : (outside : Set (Subgroup G)).MapsTo (fun Q ↦ Q ⊓ M) upperLayer := by
            intro Q hQ
            have hQo := Finset.mem_filter.mp hQ
            have hQl := mem_primePowerLayer.mp hQo.1
            have hsup : M ⊔ Q = ⊤ := by
              apply hMcoatom.2
              refine lt_of_le_of_ne le_sup_left ?_
              intro heq
              exact hQo.2 (le_sup_right.trans_eq heq.symm)
            have hVrelQ : (Q ⊓ M).relIndex Q = p := by
              calc
                (Q ⊓ M).relIndex Q = M.relIndex Q := by
                  simpa [inf_comm] using M.inf_relIndex_right Q
                _ = M.relIndex (M ⊔ Q) := (Q.relIndex_sup_left M).symm
                _ = p := by rw [hsup, Subgroup.relIndex_top_right, hMindex]
            have hVrelM : (Q ⊓ M).relIndex M = p ^ (k + 1) := by
              have htowerM := (Q ⊓ M).relIndex_mul_index inf_le_right
              have htowerQ := (Q ⊓ M).relIndex_mul_index inf_le_left
              have hQindex : Q.index = p ^ (k + 1) := by
                rw [← Subgroup.relIndex_top_right]
                exact hQl.2.2
              apply Nat.mul_right_cancel hp.pos
              calc
                (Q ⊓ M).relIndex M * p = (Q ⊓ M).index := by
                  simpa [hMindex] using htowerM
                _ = (Q ⊓ M).relIndex Q * Q.index := htowerQ.symm
                _ = p * p ^ (k + 1) := by rw [hVrelQ, hQindex]
                _ = p ^ (k + 1) * p := by ac_rfl
            apply mem_primePowerLayer.mpr
            exact ⟨le_inf hQl.1 hTM, inf_le_right, hVrelM⟩
          have houtside : outside.card ≤ p ^ (k + 1) * qBinom p a (k + 1) := by
            rw [Finset.card_eq_sum_card_fiberwise hout_maps]
            calc
              ∑ V ∈ upperLayer, (outside.filter fun Q ↦ Q ⊓ M = V).card ≤
                  ∑ _V ∈ upperLayer, p ^ (k + 1) := by
                    apply Finset.sum_le_sum
                    intro V hV
                    let actualFiber := outside.filter fun Q ↦ Q ⊓ M = V
                    let embed (Q : ↑actualFiber) : CoatomFiber M V := by
                      have hQf := Finset.mem_filter.mp Q.2
                      have hQo := Finset.mem_filter.mp hQf.1
                      exact ⟨Q.1, hQf.2, hQo.2⟩
                    have hembed : Function.Injective embed := by
                      intro Q R hQR
                      apply Subtype.ext
                      exact congrArg (fun X : CoatomFiber M V ↦ X.1) hQR
                    have hactual : actualFiber.card ≤ Fintype.card (CoatomFiber M V) := by
                      rw [← Fintype.card_coe]
                      exact Fintype.card_le_of_injective embed hembed
                    have hVmem := mem_primePowerLayer.mp hV
                    exact hactual.trans
                      ((coatomFiber_card_le_relIndex M V hMcoatom hVmem.2.1).trans_eq
                        hVmem.2.2)
              _ = upperLayer.card * p ^ (k + 1) :=
                    Finset.sum_const_nat fun _ _ ↦ rfl
              _ ≤ qBinom p a (k + 1) * p ^ (k + 1) := by
                    gcongr
                    rw [primePowerLayer_card_subgroup hTM]
                    exact ih (G := M) (hG.to_subgroup M) (T.subgroupOf M) (by
                      simpa using
                        (Subgroup.relIndex_subgroupOf (H := T) (K := M) (L := M)
                          le_rfl).trans hTrelM) (k + 1)
              _ = p ^ (k + 1) * qBinom p a (k + 1) := by ac_rfl
          rw [← hsplit]
          calc
            inside.card + outside.card ≤
                qBinom p a k + p ^ (k + 1) * qBinom p a (k + 1) :=
              Nat.add_le_add hinside houtside
            _ = qBinom p (a + 1) (k + 1) := (qBinom_succ_succ p a k).symm
end SharpIntermediateSubgroupBounds
