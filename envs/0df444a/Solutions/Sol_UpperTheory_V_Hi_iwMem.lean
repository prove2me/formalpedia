-- Prove2me | solution 1 for UpperTheory.V.Hi.iwMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:51.376623+00:00
-- url     : https://prove2.me/submissions/9514bc72-3748-4dcd-8918-2d925d00cbbe

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_OrdinaryHeckeCharacters_IwMemMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing Matrix UpperTheory.V.Hi
private theorem iwMem_mul {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) {a b : G} (ha : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a = x * t * y)
    (hb : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, b = x * t * y) :
    ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a * b = x * t * y := by
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := ha
  obtain ⟨x', hx', t', ht', y', hy', rfl⟩ := hb
  obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y hy x' hx'
  refine ⟨x * (t * x2 * t⁻¹), mul_mem hx (I.T_N t (hS ht) x2 hx2), t * s * t',
    mul_mem (mul_mem ht (hc hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
    mul_mem (I.T_Nm c t'⁻¹ (inv_mem (hS ht')) y2 hy2) hy', ?_⟩
  calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
    _ = x * t * (x2 * s * y2) * t' * y' := by rw [h]
    _ = _ := by group
private theorem iwMem_gen {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) (g : G) :
    g ∈ I.N ⊔ S ⊔ I.Nm c ↔ ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y := by
  constructor
  · intro hg
    have hN : ∀ x ∈ I.N, ∃ x' ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, x = x' * t * y :=
      fun x hx => ⟨x, hx, 1, S.one_mem, 1, (I.Nm c).one_mem, by simp⟩
    have hT : ∀ t ∈ S, ∃ x ∈ I.N, ∃ t' ∈ S, ∃ y ∈ I.Nm c, t = x * t' * y :=
      fun t ht => ⟨1, I.N.one_mem, t, ht, 1, (I.Nm c).one_mem, by simp⟩
    have hY : ∀ y ∈ I.Nm c, ∃ x ∈ I.N, ∃ t ∈ S, ∃ y' ∈ I.Nm c, y = x * t * y' :=
      fun y hy => ⟨1, I.N.one_mem, 1, S.one_mem, y, hy, by simp⟩
    let M : Subgroup G :=
      { carrier := {g | ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y}
        mul_mem' := fun ha hb => iwMem_mul I c S hS hc ha hb
        one_mem' := hN 1 I.N.one_mem
        inv_mem' := by
          rintro g ⟨x, hx, t, ht, y, hy, rfl⟩
          have e : (x * t * y)⁻¹ = y⁻¹ * t⁻¹ * x⁻¹ := by group
          rw [e]
          exact iwMem_mul I c S hS hc
            (iwMem_mul I c S hS hc (hY _ ((I.Nm c).inv_mem hy)) (hT _ (S.inv_mem ht)))
            (hN _ (I.N.inv_mem hx)) }
    have hle : I.N ⊔ S ⊔ I.Nm c ≤ M :=
      sup_le (sup_le (fun x hx => hN x hx) (fun t ht => hT t ht)) (fun y hy => hY y hy)
    exact hle hg
  · rintro ⟨x, hx, t, ht, y, hy, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ht))) (Subgroup.mem_sup_right hy)
end

set_option autoImplicit false
open IsLocalRing Matrix UpperTheory.V.Hi
namespace UpperTheory.V.Hi
theorem _root_.solution :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ) (g : G), (g ∈ I.Iw c ↔ ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.I1 c ↔ ∃ x ∈ I.N, ∃ t ∈ I.Tc c, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.Nf → g ∈ I.Iw c → g ∈ I.N) := by
  intro G _ I c g
  refine ⟨iwMem_gen I c I.T le_rfl (I.Tc_le c) g,
    iwMem_gen I c (I.Tc c) (I.Tc_le c) le_rfl g, ?_⟩
  intro hg hw
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem_gen I c I.T le_rfl (I.Tc_le c) _).1 hw
  have hy0 : y ∈ I.Nm 0 := I.Nm_anti (Nat.zero_le c) hy
  have h := I.uniq ((x * t * y)⁻¹ * x) (I.Nf.mul_mem (I.Nf.inv_mem hg) (I.N_le hx)) t
    (I.T_le ht) y hy0 (by group)
  have e : x * t * y = x := by
    calc x * t * y = x * ((x * t * y)⁻¹ * x)⁻¹ := by group
      _ = x := by rw [h.1]; group
  rw [e]
  exact hx
end UpperTheory.V.Hi
