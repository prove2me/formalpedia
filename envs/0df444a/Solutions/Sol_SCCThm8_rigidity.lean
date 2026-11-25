-- Prove2me | solution 1 for SCCThm8.rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:59:19.160397+00:00
-- url     : https://prove2.me/submissions/8024562f-d841-4da9-a57d-1adc1c2d397e

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_dl_spec
public import Theorems.Thm_SCCThm8_Rig_f3_swap
public import Theorems.Thm_SCCThm8_Rig_gg_rel
public import Theorems.Thm_SCCThm8_Rig_gg_comm
public import Theorems.Thm_SCCThm8_Rig_core

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C = psi g (fun i => mult A B C i - 1) := by
  have hs := Rig.dl_spec (f₂ := f₂) (f₃ := f₃) hk hP
  set d := Rig.dl k f₁ with hd
  let o : Fin (3 * k) := ⟨0, by omega⟩
  set g := Rig.gg d o with hg
  have hgc : ∀ i j, Commute (g i) (g j) := Rig.gg_comm hk hs o
  have hgr : ∀ i j, i ≠ j → d i j = g j * (g i)⁻¹ := fun i j hij => Rig.gg_rel hk hs o hij
  refine ⟨g, hgc, ?_⟩
  intro A B C hA hB hC
  let H := Subgroup.closure (Set.range g)
  have hcomm : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (hgc i j).eq
  have hH : ∀ x y : H, x * y = y * x := fun x y =>
    (Subgroup.isMulCommutative_closure hcomm).is_comm.comm x y
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hH }
  let g' : Fin (3 * k) → H := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let φ : H →* G := H.subtype
  have hφ : ∀ i, φ (g' i) = g i := fun i => rfl
  have hs1 : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A →
      f₁ (Rig.sw A i j) = φ (g' j * (g' i)⁻¹) * f₁ A := by
    intro A hA i j hi hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [hs A hA i j hi hj, hgr i j hij, map_mul, map_inv, hφ, hφ]
  have hs3 : ∀ C : Finset (Fin (3 * k)), C.card = k → ∀ j i, j ∈ C → i ∉ C →
      f₃ (Rig.sw C j i) = f₃ C * φ (g' i * (g' j)⁻¹) := by
    intro C hC j i hj hi
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Rig.f3_swap (f₂ := f₂) hk hP C hC j i hj hi, ← hd, hgr i j hij, map_mul, map_inv, hφ, hφ,
      mul_inv_rev, inv_inv]
  rw [Rig.core hP φ g' hs1 hs3 A B C hA hB hC, psi, Fin.prod_univ_def, map_list_prod, List.map_map]
  congr 1
end SCCThm8
