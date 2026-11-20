-- Prove2me | solution 1 for P010.isolated_member_forces_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:36:46.727933+00:00
-- url     : https://prove2.me/submissions/7ec54b36-2afb-40f9-bbd7-f947daf6926e

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (p : ℕ) :
    ∀ a : List ℕ, NonCoprimeChain a → a.Nodup →
      p ∈ a → (∀ x ∈ a, x ≠ p → Nat.Coprime p x) → a = [p] := by
  intro a
  induction a with
  | nil =>
      intro _ _ hmem _
      simp at hmem
  | cons x xs ih =>
      intro hchain hnodup hmem hiso
      cases xs with
      | nil =>
          have hpx : p = x := by simpa using hmem
          subst x
          rfl
      | cons y ys =>
          have hxy : ¬Nat.Coprime x y :=
            (List.isChain_cons.mp hchain).1 y (by simp)
          by_cases hpx : p = x
          · have hy_ne : y ≠ p := by
              intro heq
              exact (List.nodup_cons.mp hnodup).1 (by simp [hpx, heq])
            have hc : Nat.Coprime x y := by
              simpa [hpx] using hiso y (by simp) hy_ne
            exact (hxy hc).elim
          · have hmemtail : p ∈ y :: ys := by
              rcases List.mem_cons.mp hmem with heq | ht
              · exact (hpx heq).elim
              · exact ht
            have htail : NonCoprimeChain (y :: ys) :=
              (List.isChain_cons.mp hchain).2
            have hnoduptail : (y :: ys).Nodup :=
              (List.nodup_cons.mp hnodup).2
            have hisotail : ∀ z ∈ y :: ys, z ≠ p → Nat.Coprime p z := by
              intro z hz hne
              exact hiso z (by simp [hz]) hne
            have htail_eq : y :: ys = [p] :=
              ih htail hnoduptail hmemtail hisotail
            have hy : y = p := by
              have hm : y ∈ [p] := by rw [← htail_eq]; simp
              simpa using hm
            have hx_ne : x ≠ p := by
              intro heq
              exact hpx heq.symm
            have hc : Nat.Coprime x y := by
              simpa [hy] using (hiso x (by simp) hx_ne).symm
            exact (hxy hc).elim
end P010
