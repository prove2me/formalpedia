-- Prove2me | solution 1 for SCCThm8.power_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:06:23.46264+00:00
-- url     : https://prove2.me/submissions/8512b924-ab8d-40fa-8609-94ed7a44dd6a

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_D_spec
public import Theorems.Thm_SCCThm8_PRig_f3_swapP
public import Theorems.Thm_SCCThm8_PRig_blk
public import Theorems.Thm_SCCThm8_PRig_D_cross
public import Theorems.Thm_SCCThm8_PRig_coreP
public import Theorems.Thm_SCCThm8_Rig_exists_kset
public import Theorems.Thm_SCCThm8_Rig_gg_comm
public import Theorems.Thm_SCCThm8_Rig_gg_rel


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G)
    (hP : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
      f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin m → Fin (3 * k) → G, (∀ j i j' i', Commute (g j i) (g j' i')) ∧
      ∀ A B C : Fin m → Finset (Fin (3 * k)),
        (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
        f₁ A * f₂ B * f₃ C = psiP g (fun j i => multP A B C j i - 1) := by
  have hP' : PRig.Good k f₁ f₂ f₃ := hP
  set D := PRig.D k f₁ with hD
  obtain ⟨X₀, hX₀, -, -⟩ := Rig.exists_kset (k := k) (∅ : Finset (Fin (3 * k))) ∅ (by simp)
    (by simp) (by simp; omega)
  let A₀ : Fin m → Finset (Fin (3 * k)) := fun _ => X₀
  have hb := PRig.blk hk hP' A₀ (fun _ => hX₀)
  let o : Fin (3 * k) := ⟨0, by omega⟩
  let g : Fin m → Fin (3 * k) → G := fun j => Rig.gg (D j) o
  have hgr : ∀ j s t, s ≠ t → D j s t = g j t * (g j s)⁻¹ := fun j s t h =>
    Rig.gg_rel (F := fun X => f₁ (Function.update A₀ j X)) hk (hb j) o h
  have hgc : ∀ j i j' i', Commute (g j i) (g j' i') := by
    intro j i j' i'
    rcases eq_or_ne j j' with rfl | hjj
    · exact Rig.gg_comm (F := fun X => f₁ (Function.update A₀ j X)) hk (hb j) o i i'
    · simp only [g, Rig.gg]
      split_ifs with h1 h2 h2
      · exact Commute.one_left _
      · exact Commute.one_left _
      · exact Commute.one_right _
      · exact PRig.D_cross hk hP' hjj (Ne.symm h1) (Ne.symm h2)
  refine ⟨g, hgc, ?_⟩
  intro A B C hA hB hC
  let H := Subgroup.closure (Set.range fun p : Fin m × Fin (3 * k) => g p.1 p.2)
  have hcomm : ∀ x ∈ (Set.range fun p : Fin m × Fin (3 * k) => g p.1 p.2), ∀ y ∈ (Set.range fun p : Fin m × Fin (3 * k) => g p.1 p.2), x * y = y * x := by
    rintro _ ⟨⟨j, i⟩, rfl⟩ _ ⟨⟨j', i'⟩, rfl⟩; exact (hgc j i j' i').eq
  have hH : ∀ x y : H, x * y = y * x := fun x y =>
    (Subgroup.isMulCommutative_closure hcomm).is_comm.comm x y
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hH }
  let g' : Fin m → Fin (3 * k) → H := fun j i => ⟨g j i, Subgroup.subset_closure ⟨(j, i), rfl⟩⟩
  let φ : H →* G := H.subtype
  have hφ : ∀ j i, φ (g' j i) = g j i := fun j i => rfl
  have hs1 : ∀ A : Fin m → Finset (Fin (3 * k)), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j →
      t ∉ A j → f₁ (Function.update A j (Rig.sw (A j) s t)) = φ (g' j t * (g' j s)⁻¹) * f₁ A := by
    intro A hA j s t hs ht
    have hst : s ≠ t := fun h => ht (h ▸ hs)
    rw [PRig.D_spec hk hP' A hA j s t hs ht, ← hD, hgr j s t hst, map_mul, map_inv, hφ, hφ]
  have hs3 : ∀ C : Fin m → Finset (Fin (3 * k)), (∀ j, (C j).card = k) → ∀ j t s, t ∈ C j →
      s ∉ C j → f₃ (Function.update C j (Rig.sw (C j) t s)) = f₃ C * φ (g' j s * (g' j t)⁻¹) := by
    intro C hC j t s ht hs
    have hst : s ≠ t := fun h => hs (h ▸ ht)
    rw [PRig.f3_swapP hk hP' C hC j t s ht hs, ← hD, hgr j s t hst, map_mul, map_inv, hφ, hφ,
      mul_inv_rev, inv_inv]
  rw [PRig.coreP hP' φ g' hs1 hs3 A B C hA hB hC, psiP, Fin.prod_univ_def, map_list_prod,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [psi, Fin.prod_univ_def, map_list_prod, List.map_map]
  rfl
end SCCThm8
