-- Prove2me | solution 1 for PalomarZF207.henkin_completeness
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:18:25.703965+00:00
-- url     : https://prove2.me/submissions/1d9c2055-ee14-4cc7-8b40-5e0af299e1fe

import Definitions.Def_palomar_zf207_zf

open PalomarZF207

namespace DevHenkin

attribute [local instance] Classical.propDecidable

/-! ### 1. Renaming and Bound lemmas -/

private theorem lift_id : ∀ i, lift id i = i
  | 0 => rfl
  | _ + 1 => rfl

private theorem rename_id : ∀ f : Formula, rename id f = f
  | .bot => rfl
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .and a b => by simp [rename, rename_id a, rename_id b]
  | .or a b => by simp [rename, rename_id a, rename_id b]
  | .imp a b => by simp [rename, rename_id a, rename_id b]
  | .all a => by
    have h : lift id = id := funext lift_id
    simp [rename, h, rename_id a]
  | .ex a => by
    have h : lift id = id := funext lift_id
    simp [rename, h, rename_id a]

private theorem lift_comp (σ τ : Nat → Nat) : ∀ i, lift σ (lift τ i) = lift (fun k => σ (τ k)) i
  | 0 => rfl
  | _ + 1 => rfl

private theorem rename_comp (σ τ : Nat → Nat) :
    ∀ f : Formula, rename σ (rename τ f) = rename (fun i => σ (τ i)) f
  | .bot => rfl
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .and a b => by simp [rename, rename_comp σ τ a, rename_comp σ τ b]
  | .or a b => by simp [rename, rename_comp σ τ a, rename_comp σ τ b]
  | .imp a b => by simp [rename, rename_comp σ τ a, rename_comp σ τ b]
  | .all a => by
    have h : (fun i => lift σ (lift τ i)) = lift (fun k => σ (τ k)) := funext (lift_comp σ τ)
    simp [rename, rename_comp (lift σ) (lift τ) a, h]
  | .ex a => by
    have h : (fun i => lift σ (lift τ i)) = lift (fun k => σ (τ k)) := funext (lift_comp σ τ)
    simp [rename, rename_comp (lift σ) (lift τ) a, h]

private theorem rename_congr_bound :
    ∀ (f : Formula) (n : Nat) (σ τ : Nat → Nat),
      Bound f n → (∀ i < n, σ i = τ i) → rename σ f = rename τ f
  | .bot, _, _, _, _, _ => rfl
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => by simp [rename, h i hi, h j hj]
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => by simp [rename, h i hi, h j hj]
  | .and a b, n, σ, τ, ⟨ha, hb⟩, h => by
    simp [rename, rename_congr_bound a n σ τ ha h, rename_congr_bound b n σ τ hb h]
  | .or a b, n, σ, τ, ⟨ha, hb⟩, h => by
    simp [rename, rename_congr_bound a n σ τ ha h, rename_congr_bound b n σ τ hb h]
  | .imp a b, n, σ, τ, ⟨ha, hb⟩, h => by
    simp [rename, rename_congr_bound a n σ τ ha h, rename_congr_bound b n σ τ hb h]
  | .all a, n, σ, τ, ha, h => by
    simp only [rename]
    congr 1
    apply rename_congr_bound a (n + 1) (lift σ) (lift τ) ha
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp [lift, h k (Nat.lt_of_succ_lt_succ hi)]
  | .ex a, n, σ, τ, ha, h => by
    simp only [rename]
    congr 1
    apply rename_congr_bound a (n + 1) (lift σ) (lift τ) ha
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp [lift, h k (Nat.lt_of_succ_lt_succ hi)]

private theorem bound_mono : ∀ (f : Formula) {m n : Nat}, Bound f m → m ≤ n → Bound f n
  | .bot, _, _, _, _ => trivial
  | .mem _ _, _, _, ⟨h1, h2⟩, hle => ⟨Nat.lt_of_lt_of_le h1 hle, Nat.lt_of_lt_of_le h2 hle⟩
  | .eq _ _, _, _, ⟨h1, h2⟩, hle => ⟨Nat.lt_of_lt_of_le h1 hle, Nat.lt_of_lt_of_le h2 hle⟩
  | .and a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .or a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .imp a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .all a, _, _, h1, hle => bound_mono a h1 (Nat.succ_le_succ hle)
  | .ex a, _, _, h1, hle => bound_mono a h1 (Nat.succ_le_succ hle)

private theorem bound_rename :
    ∀ (f : Formula) (m n : Nat) (σ : Nat → Nat),
      Bound f m → (∀ i < m, σ i < n) → Bound (rename σ f) n
  | .bot, _, _, _, _, _ => trivial
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .and a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .or a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .imp a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .all a, m, n, σ, ha, h => by
    apply bound_rename a (m + 1) (n + 1) (lift σ) ha
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ n
    | succ k => exact Nat.succ_lt_succ (h k (Nat.lt_of_succ_lt_succ hi))
  | .ex a, m, n, σ, ha, h => by
    apply bound_rename a (m + 1) (n + 1) (lift σ) ha
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ n
    | succ k => exact Nat.succ_lt_succ (h k (Nat.lt_of_succ_lt_succ hi))

private theorem bound_allPrefix : ∀ (n m : Nat) (f : Formula), Bound f (m + n) → Bound (allPrefix n f) m
  | 0, _, _, h => h
  | n + 1, m, f, h => bound_allPrefix n (m + 1) f (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

private theorem bound_fixedAxiom {p : Formula} (h : FixedAxiom p) : Bound p 0 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [fixedRefl, fixedSym, fixedTrans, fixedEqElem, fixedExt, fixedEmpty, fixedPair,
      fixedUnion, fixedPower, fixedOmega, fixedFoundation, Bound]

private theorem bound_axiom {p : Formula} (h : Axiom p) : Bound p 0 := by
  rcases h with hf | ⟨n, body, hbd, rfl⟩ | ⟨n, body, hbd, rfl⟩
  · exact bound_fixedAxiom hf
  · apply bound_allPrefix n 0
    have hren : Bound (rename sepIndex body) (0 + n + 1 + 1 + 1) := by
      apply bound_rename body (n + 1) (0 + n + 1 + 1 + 1) sepIndex hbd
      intro i hi
      unfold sepIndex
      split <;> omega
    refine ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, hren⟩⟩,
      ⟨⟨⟨by omega, by omega⟩, hren⟩, ⟨by omega, by omega⟩⟩⟩
  · apply bound_allPrefix n 0
    have ha : Bound (rename repAIndex body) (0 + n + 1 + 1 + 1) := by
      apply bound_rename body (n + 2) (0 + n + 1 + 1 + 1) repAIndex hbd
      intro i hi
      unfold repAIndex
      split
      · omega
      · split <;> omega
    have hb : Bound (rename repBIndex body) (0 + n + 1 + 1 + 1) := by
      apply bound_rename body (n + 2) (0 + n + 1 + 1 + 1) repBIndex hbd
      intro i hi
      unfold repBIndex
      split
      · omega
      · split <;> omega
    have hc : Bound (rename repCIndex body) (0 + n + 1 + 1 + 1 + 1) := by
      apply bound_rename body (n + 2) (0 + n + 1 + 1 + 1 + 1) repCIndex hbd
      intro i hi
      unfold repCIndex
      split
      · omega
      · split <;> omega
    refine ⟨⟨ha, ⟨hb, ⟨by omega, by omega⟩⟩⟩,
      ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, hc⟩⟩,
       ⟨⟨⟨by omega, by omega⟩, hc⟩, ⟨by omega, by omega⟩⟩⟩⟩

private def boundOf : Formula → Nat
  | .bot => 0
  | .mem i j => max (i + 1) (j + 1)
  | .eq i j => max (i + 1) (j + 1)
  | .and a b => max (boundOf a) (boundOf b)
  | .or a b => max (boundOf a) (boundOf b)
  | .imp a b => max (boundOf a) (boundOf b)
  | .all a => boundOf a
  | .ex a => boundOf a

private theorem bound_boundOf : ∀ f : Formula, Bound f (boundOf f)
  | .bot => trivial
  | .mem i j => ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_left _ _),
      Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_max_right _ _)⟩
  | .eq i j => ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_left _ _),
      Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_max_right _ _)⟩
  | .and a b => ⟨bound_mono a (bound_boundOf a) (Nat.le_max_left _ _),
      bound_mono b (bound_boundOf b) (Nat.le_max_right _ _)⟩
  | .or a b => ⟨bound_mono a (bound_boundOf a) (Nat.le_max_left _ _),
      bound_mono b (bound_boundOf b) (Nat.le_max_right _ _)⟩
  | .imp a b => ⟨bound_mono a (bound_boundOf a) (Nat.le_max_left _ _),
      bound_mono b (bound_boundOf b) (Nat.le_max_right _ _)⟩
  | .all a => bound_mono a (bound_boundOf a) (Nat.le_succ _)
  | .ex a => bound_mono a (bound_boundOf a) (Nat.le_succ _)

private def listBound : List Formula → Nat
  | [] => 0
  | f :: fs => max (boundOf f) (listBound fs)

private theorem bound_of_mem_listBound :
    ∀ {Γ : List Formula} {g : Formula}, g ∈ Γ → Bound g (listBound Γ)
  | f :: _, _, .head _ => bound_mono f (bound_boundOf f) (Nat.le_max_left _ _)
  | _ :: _, g, .tail _ h => bound_mono g (bound_of_mem_listBound h) (Nat.le_max_right _ _)

/-! ### 2. Renaming in ND and basic ND derivations -/

private def renameRow (σ : Nat → Nat) : Row → Row
  | .seq Γ a => .seq (Γ.map (rename σ)) (rename σ a)
  | .branches Γ a b c => .branches (Γ.map (rename σ)) (rename σ a) (rename σ b) (rename σ c)

private theorem shift_rename (σ : Nat → Nat) (f : Formula) :
    rename (lift σ) (shift f) = shift (rename σ f) := by
  unfold shift
  rw [rename_comp, rename_comp]
  rfl

private theorem shiftContext_map_rename (σ : Nat → Nat) (Γ : Context) :
    (shiftContext Γ).map (rename (lift σ)) = shiftContext (Γ.map (rename σ)) := by
  induction Γ with
  | nil => rfl
  | cons g gs ih =>
    simp only [shiftContext, List.map_cons] at ih ⊢
    rw [shift_rename, ih]

private theorem rename_subst (σ : Nat → Nat) (t : Nat) (f : Formula) :
    rename σ (subst t f) = subst (σ t) (rename (lift σ) f) := by
  unfold subst
  rw [rename_comp, rename_comp]
  have hfn : (fun i => σ (substMap t i)) = (fun i => substMap (σ t) (lift σ i)) := by
    funext i
    cases i <;> rfl
  rw [hfn]

private theorem nd_rename : ∀ {r : Row} (σ : Nat → Nat), ND r → ND (renameRow σ r)
  | _, σ, .ctx hmem => ND.ctx (List.mem_map_of_mem hmem)
  | _, σ, .pc _ a b => ND.pc _ (rename σ a) (rename σ b)
  | _, σ, .ii h => ND.ii (nd_rename σ h)
  | _, σ, .ie h1 h2 => ND.ie (nd_rename σ h1) (nd_rename σ h2)
  | _, σ, .exp h => ND.exp (nd_rename σ h)
  | _, σ, .ci h1 h2 => ND.ci (nd_rename σ h1) (nd_rename σ h2)
  | _, σ, .ce1 h => ND.ce1 (nd_rename σ h)
  | _, σ, .ce2 h => ND.ce2 (nd_rename σ h)
  | _, σ, .di1 h => ND.di1 (nd_rename σ h)
  | _, σ, .di2 h => ND.di2 (nd_rename σ h)
  | _, σ, .branchPair h1 h2 => ND.branchPair (nd_rename σ h1) (nd_rename σ h2)
  | _, σ, .de h1 h2 => ND.de (nd_rename σ h1) (nd_rename σ h2)
  | _, σ, .wk hsub h =>
    ND.wk (fun a ha => by
      rcases List.mem_map.mp ha with ⟨g, hg, rfl⟩
      exact List.mem_map_of_mem (hsub g hg)) (nd_rename σ h)
  | _, σ, .allI h => by
    apply ND.allI
    rw [← shiftContext_map_rename]
    exact nd_rename (lift σ) h
  | _, σ, .allE t h => by
    change ND (.seq _ (rename σ (subst t _)))
    rw [rename_subst]
    exact ND.allE (σ t) (nd_rename σ h)
  | _, σ, .exI t h => by
    apply ND.exI (σ t)
    rw [← rename_subst]
    exact nd_rename σ h
  | _, σ, .exE h1 h2 => by
    apply ND.exE (nd_rename σ h1)
    have h2' := nd_rename (lift σ) h2
    change ND (.seq (rename (lift σ) _ :: (shiftContext _).map (rename (lift σ)))
      (rename (lift σ) (shift _))) at h2'
    rw [shiftContext_map_rename, shift_rename] at h2'
    exact h2'

private theorem nd_dne {Γ : Context} {a : Formula}
    (h : ND (.seq ((.imp a .bot) :: Γ) .bot)) : ND (.seq Γ a) :=
  ND.ie (ND.pc Γ a .bot) (ND.ii (ND.exp h))

private theorem nd_not_all_imp_ex_not {Γ : Context} {a : Formula}
    (h : ND (.seq Γ (.imp (.all a) .bot))) : ND (.seq Γ (.ex (.imp a .bot))) := by
  apply nd_dne
  have hAll : ND (.seq ((.imp (.ex (.imp a .bot)) .bot) :: Γ) (.all a)) := by
    apply ND.allI
    apply nd_dne
    have hEx : ND (.seq ((.imp a .bot) :: shiftContext ((.imp (.ex (.imp a .bot)) .bot) :: Γ))
        (shift (.ex (.imp a .bot)))) := by
      have hsubst : subst 0 (rename (lift Nat.succ) (.imp a .bot)) = .imp a .bot := by
        unfold subst
        rw [rename_comp]
        have hfn : (fun i => substMap 0 (lift Nat.succ i)) = id := by
          funext i
          cases i <;> rfl
        rw [hfn, rename_id]
      change ND (.seq _ (.ex (rename (lift Nat.succ) (.imp a .bot))))
      apply ND.exI 0
      rw [hsubst]
      exact ND.ctx (.head _)
    have hNegEx : ND (.seq ((.imp a .bot) :: shiftContext ((.imp (.ex (.imp a .bot)) .bot) :: Γ))
        (.imp (shift (.ex (.imp a .bot))) .bot)) :=
      ND.ctx (.tail _ (.head _))
    exact ND.ie hNegEx hEx
  exact ND.ie (ND.wk (fun g hg => .tail _ hg) h) hAll

/-! ### 3. Surjection `Nat → Formula` -/

private def cantor (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

private def unpairAux : Nat → Nat → Nat → Nat × Nat
  | 0, s, n => (s - n, n)
  | fuel + 1, s, n =>
    if n ≤ s then (s - n, n) else unpairAux fuel (s + 1) (n - (s + 1))

private def unpair (n : Nat) : Nat × Nat := unpairAux n 0 n

private theorem tri_step (s : Nat) : (s + 1) * (s + 1 + 1) / 2 = s * (s + 1) / 2 + (s + 1) := by
  have hmul : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * (s + 1) := by
    have h1 : (s + 1) * (s + 1 + 1) = (s + 1) * s + (s + 1) * 2 := Nat.mul_add (s + 1) s 2
    have h2 : (s + 1) * s = s * (s + 1) := Nat.mul_comm (s + 1) s
    omega
  omega

private theorem unpairAux_spec : ∀ fuel s n,
    (∀ a b, n + s * (s + 1) / 2 = cantor a b → a + b ≥ s → a + b ≤ s + fuel →
      unpairAux fuel s n = (a, b))
  | 0, s, n, a, b, heq, hge, hle => by
    have hab : a + b = s := by omega
    have hns : n = b := by
      unfold cantor at heq
      rw [hab] at heq
      omega
    simp [unpairAux, hns, show s - b = a by omega]
  | fuel + 1, s, n, a, b, heq, hge, hle => by
    unfold unpairAux
    by_cases h : n ≤ s
    · have hab : a + b = s := by
        apply Classical.byContradiction
        intro hne
        have hgt : a + b ≥ s + 1 := by omega
        unfold cantor at heq
        have htri : (a + b) * (a + b + 1) / 2 ≥ (s + 1) * (s + 1 + 1) / 2 := by
          apply Nat.div_le_div_right
          exact Nat.mul_le_mul hgt (Nat.succ_le_succ hgt)
        have hstep := tri_step s
        omega
      have hnb : n = b := by
        unfold cantor at heq
        rw [hab] at heq
        omega
      rw [if_pos h, hnb, show s - b = a by omega]
    · rw [if_neg h]
      have hgt : a + b ≥ s + 1 := by
        apply Classical.byContradiction
        intro hlt
        have hab : a + b = s := by omega
        unfold cantor at heq
        rw [hab] at heq
        omega
      apply unpairAux_spec fuel (s + 1) (n - (s + 1)) a b _ hgt (by omega)
      have hstep := tri_step s
      omega

private theorem cantor_ge_sum (a b : Nat) : a + b ≤ cantor a b := by
  unfold cantor
  cases h : a + b with
  | zero => omega
  | succ k =>
    have hmul : (k + 1) * (k + 1 + 1) ≥ 2 * (k + 1) := by
      have hle : 2 ≤ k + 1 + 1 := by omega
      have := Nat.mul_le_mul_left (k + 1) hle
      omega
    omega

private theorem unpair_cantor (a b : Nat) : unpair (cantor a b) = (a, b) := by
  apply unpairAux_spec (cantor a b) 0 (cantor a b) a b
  · simp
  · omega
  · simpa using cantor_ge_sum a b

private def encodeFormula : Formula → Nat
  | .bot => 0
  | .mem i j => 1 + 8 * cantor i j
  | .eq i j => 2 + 8 * cantor i j
  | .and a b => 3 + 8 * cantor (encodeFormula a) (encodeFormula b)
  | .or a b => 4 + 8 * cantor (encodeFormula a) (encodeFormula b)
  | .imp a b => 5 + 8 * cantor (encodeFormula a) (encodeFormula b)
  | .all a => 6 + 8 * encodeFormula a
  | .ex a => 7 + 8 * encodeFormula a

private def decodeFormulaAux : Nat → Nat → Formula
  | 0, _ => .bot
  | fuel + 1, n =>
    let tag := n % 8
    let payload := n / 8
    match tag with
    | 0 => .bot
    | 1 => let p := unpair payload; .mem p.1 p.2
    | 2 => let p := unpair payload; .eq p.1 p.2
    | 3 => let p := unpair payload; .and (decodeFormulaAux fuel p.1) (decodeFormulaAux fuel p.2)
    | 4 => let p := unpair payload; .or (decodeFormulaAux fuel p.1) (decodeFormulaAux fuel p.2)
    | 5 => let p := unpair payload; .imp (decodeFormulaAux fuel p.1) (decodeFormulaAux fuel p.2)
    | 6 => .all (decodeFormulaAux fuel payload)
    | _ => .ex (decodeFormulaAux fuel payload)

private def decodeFormula (n : Nat) : Formula := decodeFormulaAux (n + 1) n

private theorem decodeFormulaAux_encode :
    ∀ (f : Formula) (fuel : Nat), encodeFormula f < fuel → decodeFormulaAux fuel (encodeFormula f) = f
  | .bot, fuel + 1, _ => rfl
  | .mem i j, fuel + 1, _ => by
    simp [encodeFormula, decodeFormulaAux, show (1 + 8 * cantor i j) % 8 = 1 by omega,
      show (1 + 8 * cantor i j) / 8 = cantor i j by omega, unpair_cantor]
  | .eq i j, fuel + 1, _ => by
    simp [encodeFormula, decodeFormulaAux, show (2 + 8 * cantor i j) % 8 = 2 by omega,
      show (2 + 8 * cantor i j) / 8 = cantor i j by omega, unpair_cantor]
  | .and a b, fuel + 1, hlt => by
    have h1 : encodeFormula a < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    have h2 : encodeFormula b < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    simp only [encodeFormula, decodeFormulaAux,
      show (3 + 8 * cantor (encodeFormula a) (encodeFormula b)) % 8 = 3 by omega,
      show (3 + 8 * cantor (encodeFormula a) (encodeFormula b)) / 8 = cantor (encodeFormula a) (encodeFormula b) by omega,
      unpair_cantor]
    rw [decodeFormulaAux_encode a fuel h1, decodeFormulaAux_encode b fuel h2]
  | .or a b, fuel + 1, hlt => by
    have h1 : encodeFormula a < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    have h2 : encodeFormula b < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    simp only [encodeFormula, decodeFormulaAux,
      show (4 + 8 * cantor (encodeFormula a) (encodeFormula b)) % 8 = 4 by omega,
      show (4 + 8 * cantor (encodeFormula a) (encodeFormula b)) / 8 = cantor (encodeFormula a) (encodeFormula b) by omega,
      unpair_cantor]
    rw [decodeFormulaAux_encode a fuel h1, decodeFormulaAux_encode b fuel h2]
  | .imp a b, fuel + 1, hlt => by
    have h1 : encodeFormula a < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    have h2 : encodeFormula b < fuel := by
      have := cantor_ge_sum (encodeFormula a) (encodeFormula b)
      simp only [encodeFormula] at hlt; omega
    simp only [encodeFormula, decodeFormulaAux,
      show (5 + 8 * cantor (encodeFormula a) (encodeFormula b)) % 8 = 5 by omega,
      show (5 + 8 * cantor (encodeFormula a) (encodeFormula b)) / 8 = cantor (encodeFormula a) (encodeFormula b) by omega,
      unpair_cantor]
    rw [decodeFormulaAux_encode a fuel h1, decodeFormulaAux_encode b fuel h2]
  | .all a, fuel + 1, hlt => by
    have h1 : encodeFormula a < fuel := by simp only [encodeFormula] at hlt; omega
    simp only [encodeFormula, decodeFormulaAux,
      show (6 + 8 * encodeFormula a) % 8 = 6 by omega,
      show (6 + 8 * encodeFormula a) / 8 = encodeFormula a by omega]
    rw [decodeFormulaAux_encode a fuel h1]
  | .ex a, fuel + 1, hlt => by
    have h1 : encodeFormula a < fuel := by simp only [encodeFormula] at hlt; omega
    simp only [encodeFormula, decodeFormulaAux,
      show (7 + 8 * encodeFormula a) % 8 = 7 by omega,
      show (7 + 8 * encodeFormula a) / 8 = encodeFormula a by omega]
    rw [decodeFormulaAux_encode a fuel h1]

private theorem decodeFormula_encode (f : Formula) : decodeFormula (encodeFormula f) = f :=
  decodeFormulaAux_encode f (encodeFormula f + 1) (Nat.lt_succ_self _)

/-! ### 4. Henkin + Lindenbaum maximal consistent set -/

private def ConsList (Δ : List Formula) : Prop :=
  ∀ Γ : Context, (∀ g, g ∈ Γ → Axiom g ∨ g ∈ Δ) → ¬ ND (.seq Γ .bot)

private theorem consList_nil (hCons : Consistent) : ConsList [] := by
  intro Γ hΓ hBot
  apply hCons
  refine ⟨Γ, fun q hq => ?_, hBot⟩
  rcases hΓ q hq with hAx | hMem
  · exact hAx
  · cases hMem

private def freshSwap (N : Nat) (i : Nat) : Nat :=
  if i = N then 0 else if i < N then i + 1 else i

private theorem rename_freshSwap_bound (N : Nat) (g : Formula) (hg : Bound g N) :
    rename (freshSwap N) g = shift g := by
  unfold shift
  apply rename_congr_bound g N (freshSwap N) Nat.succ hg
  intro i hi
  unfold freshSwap
  have hne : i ≠ N := by omega
  simp [hne, hi]

private theorem rename_freshSwap_subst (N : Nat) (a : Formula) (ha : Bound a (N + 1)) :
    rename (freshSwap N) (subst N a) = a := by
  unfold subst
  rw [rename_comp]
  conv => rhs; rw [← rename_id a]
  apply rename_congr_bound a (N + 1) (fun i => freshSwap N (substMap N i)) id ha
  intro i hi
  cases i with
  | zero => simp [substMap, freshSwap]
  | succ k =>
    have hk : k < N := Nat.lt_of_succ_lt_succ hi
    have hne : k ≠ N := by omega
    simp [substMap, freshSwap, hne, hk]

private theorem consList_add_witness {Δ : List Formula} {a : Formula}
    (hCons : ConsList (.ex a :: Δ)) :
    let N := max (boundOf (.ex a)) (listBound Δ)
    ConsList (subst N a :: .ex a :: Δ) := by
  intro N Γ hΓ hBot
  let Γ' : Context := Γ.filter (fun g => decide (g ≠ subst N a))
  have hSub : ContextSub Γ (subst N a :: .ex a :: Γ') := by
    intro g hg
    by_cases heq : g = subst N a
    · subst heq; exact .head _
    · exact .tail _ (.tail _ (List.mem_filter.mpr ⟨hg, by simp [heq]⟩))
  have hBot1 : ND (.seq (subst N a :: .ex a :: Γ') .bot) := ND.wk hSub hBot
  have hBdΓ' : ∀ g, g ∈ .ex a :: Γ' → Bound g N := by
    intro g hg
    cases hg with
    | head => exact bound_mono (.ex a) (bound_boundOf (.ex a)) (Nat.le_max_left _ _)
    | tail _ hg' =>
      have hgΓ : g ∈ Γ := (List.mem_filter.mp hg').1
      rcases hΓ g hgΓ with hAx | hMem
      · exact bound_mono g (bound_axiom hAx) (Nat.zero_le N)
      · cases hMem with
        | head => exact absurd rfl (of_decide_eq_true (List.mem_filter.mp hg').2)
        | tail _ hMem2 =>
          cases hMem2 with
          | head => exact bound_mono (.ex a) (bound_boundOf (.ex a)) (Nat.le_max_left _ _)
          | tail _ hΔ => exact bound_mono g (bound_of_mem_listBound hΔ) (Nat.le_max_right _ _)
  have haN : Bound a (N + 1) :=
    bound_mono (.ex a) (bound_boundOf (.ex a)) (Nat.le_max_left _ _)
  have hRen := nd_rename (freshSwap N) hBot1
  have hmap : ((.ex a :: Γ').map (rename (freshSwap N))) = shiftContext (.ex a :: Γ') := by
    unfold shiftContext
    apply List.map_congr_left
    intro g hg
    exact rename_freshSwap_bound N g (hBdΓ' g hg)
  change ND (.seq (rename (freshSwap N) (subst N a) :: (.ex a :: Γ').map (rename (freshSwap N)))
      (rename (freshSwap N) .bot)) at hRen
  rw [rename_freshSwap_subst N a haN, hmap] at hRen
  have hBot2 : ND (.seq (.ex a :: Γ') .bot) :=
    ND.exE (ND.ctx (.head _)) hRen
  apply hCons (.ex a :: Γ') _ hBot2
  intro g hg
  cases hg with
  | head => exact Or.inr (.head _)
  | tail _ hg' =>
    have hgΓ : g ∈ Γ := (List.mem_filter.mp hg').1
    rcases hΓ g hgΓ with hAx | hMem
    · exact Or.inl hAx
    · cases hMem with
      | head => exact absurd rfl (of_decide_eq_true (List.mem_filter.mp hg').2)
      | tail _ hMem2 => exact Or.inr hMem2

private noncomputable def henkinChain : Nat → List Formula
  | 0 => []
  | n + 1 =>
    let Δ := henkinChain n
    let φ := decodeFormula n
    if ConsList (φ :: Δ) then
      match φ with
      | .ex a => subst (max (boundOf (.ex a)) (listBound Δ)) a :: .ex a :: Δ
      | _ => φ :: Δ
    else Δ

private theorem henkinChain_mono {n : Nat} {f : Formula} (h : f ∈ henkinChain n) :
    f ∈ henkinChain (n + 1) := by
  unfold henkinChain
  dsimp only
  split
  · split
    · exact .tail _ (.tail _ h)
    · exact .tail _ h
  · exact h

private theorem henkinChain_mono_le {m n : Nat} (hle : m ≤ n) {f : Formula} (h : f ∈ henkinChain m) :
    f ∈ henkinChain n := by
  induction hle with
  | refl => exact h
  | step _ ih => exact henkinChain_mono ih

private theorem henkinChain_cons (hCons : Consistent) : ∀ n, ConsList (henkinChain n)
  | 0 => consList_nil hCons
  | n + 1 => by
    unfold henkinChain
    dsimp only
    split
    · rename_i hc
      split
      · rename_i a heq
        rw [heq] at hc
        exact consList_add_witness hc
      · exact hc
    · exact henkinChain_cons hCons n

private def MSet (f : Formula) : Prop := ∃ n, f ∈ henkinChain n

private theorem mset_finite_stage :
    ∀ Γ : Context, (∀ g, g ∈ Γ → MSet g) → ∃ n, ∀ g, g ∈ Γ → g ∈ henkinChain n
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | g :: gs, h => by
    obtain ⟨n1, hn1⟩ := h g (.head _)
    obtain ⟨n2, hn2⟩ := mset_finite_stage gs (fun x hx => h x (.tail _ hx))
    refine ⟨max n1 n2, fun x hx => ?_⟩
    cases hx with
    | head => exact henkinChain_mono_le (Nat.le_max_left _ _) hn1
    | tail _ hxs => exact henkinChain_mono_le (Nat.le_max_right _ _) (hn2 x hxs)

private theorem mset_cons (hCons : Consistent) {Γ : Context}
    (hΓ : ∀ g, g ∈ Γ → Axiom g ∨ MSet g) : ¬ ND (.seq Γ .bot) := by
  let ΓM := Γ.filter (fun g => decide (MSet g))
  have hΓM : ∀ g, g ∈ ΓM → MSet g := fun g hg => of_decide_eq_true (List.mem_filter.mp hg).2
  obtain ⟨n, hn⟩ := mset_finite_stage ΓM hΓM
  intro hBot
  apply henkinChain_cons hCons n Γ _ hBot
  intro g hg
  rcases hΓ g hg with hAx | hM
  · exact Or.inl hAx
  · exact Or.inr (hn g (List.mem_filter.mpr ⟨hg, decide_eq_true hM⟩))

private theorem mset_closed (hCons : Consistent) {Γ : Context} {f : Formula}
    (hΓ : ∀ g, g ∈ Γ → Axiom g ∨ MSet g) (hDer : ND (.seq Γ f)) : MSet f := by
  let n := encodeFormula f
  have hdec : decodeFormula n = f := decodeFormula_encode f
  have hcf : ConsList (f :: henkinChain n) := by
    intro Δ hΔ hBot
    let Δ' := Δ.filter (fun g => decide (g ≠ f))
    have hSub : ContextSub Δ (f :: Δ') := by
      intro g hg
      by_cases heq : g = f
      · subst heq; exact .head _
      · exact .tail _ (List.mem_filter.mpr ⟨hg, by simp [heq]⟩)
    have hImp : ND (.seq Δ' (.imp f .bot)) := ND.ii (ND.wk hSub hBot)
    have hBotAll : ND (.seq (Γ ++ Δ') .bot) :=
      ND.ie (ND.wk (fun g hg => List.mem_append_right Γ hg) hImp)
            (ND.wk (fun g hg => List.mem_append_left Δ' hg) hDer)
    apply mset_cons hCons (Γ := Γ ++ Δ') _ hBotAll
    intro g hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact hΓ g hg1
    · have hgΔ : g ∈ Δ := (List.mem_filter.mp hg2).1
      rcases hΔ g hgΔ with hAx | hMem
      · exact Or.inl hAx
      · cases hMem with
        | head => exact absurd rfl (of_decide_eq_true (List.mem_filter.mp hg2).2)
        | tail _ hhn => exact Or.inr ⟨n, hhn⟩
  refine ⟨n + 1, ?_⟩
  unfold henkinChain
  dsimp only
  rw [hdec, if_pos hcf]
  split
  · exact .tail _ (.head _)
  · exact .head _

private theorem mset_axiom (hCons : Consistent) {p : Formula} (hAx : Axiom p) : MSet p :=
  mset_closed hCons (Γ := [p]) (fun g hg => by cases hg with | head => exact Or.inl hAx | tail _ h => cases h)
    (ND.ctx (.head _))

private theorem mset_not_mem_iff (hCons : Consistent) (f : Formula) :
    ¬ MSet f ↔ MSet (.imp f .bot) := by
  constructor
  · intro hnf
    let n := encodeFormula f
    have hdec : decodeFormula n = f := decodeFormula_encode f
    have hnc : ¬ ConsList (f :: henkinChain n) := by
      intro hcf
      apply hnf
      refine ⟨n + 1, ?_⟩
      unfold henkinChain
      dsimp only
      rw [hdec, if_pos hcf]
      split
      · exact .tail _ (.head _)
      · exact .head _
    have hex : ∃ Γ, (∀ g, g ∈ Γ → Axiom g ∨ g ∈ f :: henkinChain n) ∧ ND (.seq Γ .bot) := by
      apply Classical.byContradiction
      intro hall
      apply hnc
      intro Γ hΓ hBot
      exact hall ⟨Γ, hΓ, hBot⟩
    obtain ⟨Γ, hΓ, hBot⟩ := hex
    let Γ' := Γ.filter (fun g => decide (g ≠ f))
    have hSub : ContextSub Γ (f :: Γ') := by
      intro g hg
      by_cases heq : g = f
      · subst heq; exact .head _
      · exact .tail _ (List.mem_filter.mpr ⟨hg, by simp [heq]⟩)
    have hImp : ND (.seq Γ' (.imp f .bot)) := ND.ii (ND.wk hSub hBot)
    apply mset_closed hCons (Γ := Γ') _ hImp
    intro g hg
    have hgΓ : g ∈ Γ := (List.mem_filter.mp hg).1
    rcases hΓ g hgΓ with hAx | hMem
    · exact Or.inl hAx
    · cases hMem with
      | head => exact absurd rfl (of_decide_eq_true (List.mem_filter.mp hg).2)
      | tail _ hhn => exact Or.inr ⟨n, hhn⟩
  · intro hNeg hf
    exact mset_cons hCons (Γ := [.imp f .bot, f])
      (fun g hg => by
        cases hg with
        | head => exact Or.inr hNeg
        | tail _ h2 => cases h2 with | head => exact Or.inr hf | tail _ h3 => cases h3)
      (ND.ie (ND.ctx (.head _)) (ND.ctx (.tail _ (.head _))))

private theorem mset_ex_witness (hCons : Consistent) {a : Formula} (h : MSet (.ex a)) :
    ∃ t : Nat, MSet (subst t a) := by
  let n := encodeFormula (.ex a)
  have hdec : decodeFormula n = .ex a := decodeFormula_encode (.ex a)
  have hcf : ConsList (.ex a :: henkinChain n) := by
    intro Δ hΔ hBot
    apply mset_cons hCons (Γ := Δ) _ hBot
    intro g hg
    rcases hΔ g hg with hAx | hMem
    · exact Or.inl hAx
    · cases hMem with
      | head => exact Or.inr h
      | tail _ hhn => exact Or.inr ⟨n, hhn⟩
  refine ⟨max (boundOf (.ex a)) (listBound (henkinChain n)), n + 1, ?_⟩
  change subst (max (boundOf (.ex a)) (listBound (henkinChain n))) a ∈ henkinChain (n + 1)
  rw [henkinChain.eq_def]
  dsimp only
  rw [hdec, if_pos hcf]
  exact .head _

/-! ### 5. Quotient Model and Truth Lemma -/

private def Eqv (i j : Nat) : Prop := MSet (.eq i j)

private theorem eqv_refl (hCons : Consistent) (i : Nat) : Eqv i i := by
  have hAx : Axiom fixedRefl := Or.inl (Or.inl rfl)
  have hDer : ND (.seq [fixedRefl] (subst i (.eq 0 0))) := ND.allE i (ND.ctx (.head _))
  exact mset_closed hCons (Γ := [fixedRefl])
    (fun g hg => by cases hg with | head => exact Or.inl hAx | tail _ h => cases h) hDer

private theorem eqv_sym (hCons : Consistent) {i j : Nat} (h : Eqv i j) : Eqv j i := by
  have hAx : Axiom fixedSym := Or.inl (Or.inr (Or.inl rfl))
  have h1 : ND (.seq [fixedSym] (.all (.imp (.eq (i + 1) 0) (.eq 0 (i + 1))))) :=
    ND.allE i (ND.ctx (.head _) : ND (.seq [fixedSym] fixedSym))
  have h2 : ND (.seq [fixedSym] (.imp (.eq i j) (.eq j i))) := ND.allE j h1
  exact mset_closed hCons (Γ := [fixedSym, .eq i j])
    (fun g hg => by
      cases hg with
      | head => exact Or.inl hAx
      | tail _ h' => cases h' with | head => exact Or.inr h | tail _ h'' => cases h'')
    (ND.ie (ND.wk (fun g hg => by cases hg with | head => exact .head _ | tail _ h' => cases h') h2)
      (ND.ctx (.tail _ (.head _))))

private theorem eqv_trans (hCons : Consistent) {i j k : Nat} (h1 : Eqv i j) (h2 : Eqv j k) :
    Eqv i k := by
  have hAx : Axiom fixedTrans := Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  have d0 : ND (.seq [fixedTrans] fixedTrans) := ND.ctx (.head _)
  have d1 := ND.allE i d0
  have d2 := ND.allE j d1
  have d3 : ND (.seq [fixedTrans] (.imp (.eq i j) (.imp (.eq j k) (.eq i k)))) := ND.allE k d2
  have d3' : ND (.seq [fixedTrans, .eq i j, .eq j k] (.imp (.eq i j) (.imp (.eq j k) (.eq i k)))) :=
    ND.wk (fun g hg => by cases hg with | head => exact .head _ | tail _ h' => cases h') d3
  have dFin : ND (.seq [fixedTrans, .eq i j, .eq j k] (.eq i k)) :=
    ND.ie (ND.ie d3' (ND.ctx (.tail _ (.head _)))) (ND.ctx (.tail _ (.tail _ (.head _))))
  exact mset_closed hCons (Γ := [fixedTrans, .eq i j, .eq j k])
    (fun g hg => by
      cases hg with
      | head => exact Or.inl hAx
      | tail _ h' => cases h' with
        | head => exact Or.inr h1
        | tail _ h'' => cases h'' with | head => exact Or.inr h2 | tail _ h''' => cases h''')
    dFin

private theorem eqv_mem_congr (hCons : Consistent) {i1 i2 j1 j2 : Nat}
    (hi : Eqv i1 i2) (hj : Eqv j1 j2) (hm : MSet (.mem i1 j1)) : MSet (.mem i2 j2) := by
  have hAx : Axiom fixedEqElem := Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have d0 : ND (.seq [fixedEqElem] fixedEqElem) := ND.ctx (.head _)
  have d1 := ND.allE i1 d0
  have d2 := ND.allE j1 d1
  have d3 := ND.allE i2 d2
  have d4 : ND (.seq [fixedEqElem] (.imp (.eq i1 i2) (.imp (.eq j1 j2) (.imp (.mem i1 j1) (.mem i2 j2))))) :=
    ND.allE j2 d3
  have d4' : ND (.seq [fixedEqElem, .eq i1 i2, .eq j1 j2, .mem i1 j1]
      (.imp (.eq i1 i2) (.imp (.eq j1 j2) (.imp (.mem i1 j1) (.mem i2 j2))))) :=
    ND.wk (fun g hg => by cases hg with | head => exact .head _ | tail _ h' => cases h') d4
  have dFin : ND (.seq [fixedEqElem, .eq i1 i2, .eq j1 j2, .mem i1 j1] (.mem i2 j2)) :=
    ND.ie (ND.ie (ND.ie d4' (ND.ctx (.tail _ (.head _))))
      (ND.ctx (.tail _ (.tail _ (.head _)))))
      (ND.ctx (.tail _ (.tail _ (.tail _ (.head _)))))
  exact mset_closed hCons (Γ := [fixedEqElem, .eq i1 i2, .eq j1 j2, .mem i1 j1])
    (fun g hg => by
      cases hg with
      | head => exact Or.inl hAx
      | tail _ h' => cases h' with
        | head => exact Or.inr hi
        | tail _ h'' => cases h'' with
          | head => exact Or.inr hj
          | tail _ h''' => cases h''' with | head => exact Or.inr hm | tail _ h4 => cases h4)
    dFin

private def henkinSetoid (hCons : Consistent) : Setoid Nat where
  r := Eqv
  iseqv := ⟨eqv_refl hCons, fun h => eqv_sym hCons h, fun h1 h2 => eqv_trans hCons h1 h2⟩

private abbrev HenkinV (hCons : Consistent) : Type := Quotient (henkinSetoid hCons)

private def HenkinE (hCons : Consistent) : HenkinV hCons → HenkinV hCons → Prop :=
  Quotient.lift₂ (fun i j => MSet (.mem i j)) (fun _ _ _ _ hi hj => propext
    ⟨fun h => eqv_mem_congr hCons hi hj h,
     fun h => eqv_mem_congr hCons (eqv_sym hCons hi) (eqv_sym hCons hj) h⟩)

private def pushNat (σ : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => t
  | n + 1 => σ n

private theorem pushValue_mk (hCons : Consistent) (σ : Nat → Nat) (t : Nat) :
    pushValue (fun i => Quotient.mk (henkinSetoid hCons) (σ i))
      (Quotient.mk (henkinSetoid hCons) t) =
    (fun i => Quotient.mk (henkinSetoid hCons) (pushNat σ t i)) := by
  funext i
  cases i <;> rfl

private theorem subst_rename_lift (σ : Nat → Nat) (t : Nat) (p : Formula) :
    subst t (rename (lift σ) p) = rename (pushNat σ t) p := by
  unfold subst
  rw [rename_comp]
  have hfn : (fun i => substMap t (lift σ i)) = pushNat σ t := by
    funext i
    cases i <;> rfl
  rw [hfn]

private theorem truth_lemma (hCons : Consistent) :
    ∀ (f : Formula) (σ : Nat → Nat),
      eval (HenkinE hCons) f (fun i => Quotient.mk (henkinSetoid hCons) (σ i)) ↔
        MSet (rename σ f)
  | .bot, _ => by
    constructor
    · intro h; exact False.elim h
    · intro h
      exact mset_cons hCons (Γ := [.bot])
        (fun g hg => by cases hg with | head => exact Or.inr h | tail _ h' => cases h')
        (ND.ctx (.head _))
  | .mem i j, σ => Iff.rfl
  | .eq i j, σ => by
    change Quotient.mk (henkinSetoid hCons) (σ i) = Quotient.mk (henkinSetoid hCons) (σ j) ↔
      MSet (.eq (σ i) (σ j))
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := henkinSetoid hCons) h⟩
  | .and a b, σ => by
    simp only [eval, truth_lemma hCons a σ, truth_lemma hCons b σ]
    constructor
    · rintro ⟨ha, hb⟩
      exact mset_closed hCons (Γ := [rename σ a, rename σ b])
        (fun g hg => by
          cases hg with
          | head => exact Or.inr ha
          | tail _ h' => cases h' with | head => exact Or.inr hb | tail _ h'' => cases h'')
        (ND.ci (ND.ctx (.head _)) (ND.ctx (.tail _ (.head _))))
    · intro hab
      constructor
      · exact mset_closed hCons (Γ := [.and (rename σ a) (rename σ b)])
          (fun g hg => by cases hg with | head => exact Or.inr hab | tail _ h' => cases h')
          (ND.ce1 (ND.ctx (.head _)))
      · exact mset_closed hCons (Γ := [.and (rename σ a) (rename σ b)])
          (fun g hg => by cases hg with | head => exact Or.inr hab | tail _ h' => cases h')
          (ND.ce2 (ND.ctx (.head _)))
  | .or a b, σ => by
    simp only [eval, truth_lemma hCons a σ, truth_lemma hCons b σ]
    constructor
    · intro h
      cases h with
      | inl ha =>
        exact mset_closed hCons (Γ := [rename σ a])
          (fun g hg => by cases hg with | head => exact Or.inr ha | tail _ h' => cases h')
          (ND.di1 (ND.ctx (.head _)))
      | inr hb =>
        exact mset_closed hCons (Γ := [rename σ b])
          (fun g hg => by cases hg with | head => exact Or.inr hb | tail _ h' => cases h')
          (ND.di2 (ND.ctx (.head _)))
    · intro hor
      apply Classical.byContradiction
      intro hnot
      have hna : MSet (.imp (rename σ a) .bot) :=
        (mset_not_mem_iff hCons _).mp (fun ha => hnot (Or.inl ha))
      have hnb : MSet (.imp (rename σ b) .bot) :=
        (mset_not_mem_iff hCons _).mp (fun hb => hnot (Or.inr hb))
      have hBot : ND (.seq [.or (rename σ a) (rename σ b), .imp (rename σ a) .bot, .imp (rename σ b) .bot] .bot) :=
        ND.de (ND.ctx (.head _))
          (ND.branchPair
            (ND.ie (ND.ctx (.tail _ (.tail _ (.head _)))) (ND.ctx (.head _)))
            (ND.ie (ND.ctx (.tail _ (.tail _ (.tail _ (.head _))))) (ND.ctx (.head _))))
      exact mset_cons hCons (Γ := [.or (rename σ a) (rename σ b), .imp (rename σ a) .bot, .imp (rename σ b) .bot])
        (fun g hg => by
          cases hg with
          | head => exact Or.inr hor
          | tail _ h1 => cases h1 with
            | head => exact Or.inr hna
            | tail _ h2 => cases h2 with | head => exact Or.inr hnb | tail _ h3 => cases h3)
        hBot
  | .imp a b, σ => by
    simp only [eval, truth_lemma hCons a σ, truth_lemma hCons b σ]
    constructor
    · intro h
      cases Classical.em (MSet (rename σ a)) with
      | inl ha =>
        have hb := h ha
        exact mset_closed hCons (Γ := [rename σ b])
          (fun g hg => by cases hg with | head => exact Or.inr hb | tail _ h' => cases h')
          (ND.ii (ND.ctx (.tail _ (.head _))))
      | inr hna =>
        have hna' := (mset_not_mem_iff hCons _).mp hna
        exact mset_closed hCons (Γ := [.imp (rename σ a) .bot])
          (fun g hg => by cases hg with | head => exact Or.inr hna' | tail _ h' => cases h')
          (ND.ii (ND.exp (ND.ie (ND.ctx (.tail _ (.head _))) (ND.ctx (.head _)))))
    · intro hab ha
      exact mset_closed hCons (Γ := [.imp (rename σ a) (rename σ b), rename σ a])
        (fun g hg => by
          cases hg with
          | head => exact Or.inr hab
          | tail _ h' => cases h' with | head => exact Or.inr ha | tail _ h'' => cases h'')
        (ND.ie (ND.ctx (.head _)) (ND.ctx (.tail _ (.head _))))
  | .all p, σ => by
    constructor
    · intro h
      apply Classical.byContradiction
      intro hna
      have hNeg := (mset_not_mem_iff hCons _).mp hna
      have hExNeg : MSet (.ex (.imp (rename (lift σ) p) .bot)) :=
        mset_closed hCons (Γ := [.imp (.all (rename (lift σ) p)) .bot])
          (fun g hg => by cases hg with | head => exact Or.inr hNeg | tail _ h' => cases h')
          (nd_not_all_imp_ex_not (ND.ctx (.head _)))
      obtain ⟨t, ht⟩ := mset_ex_witness hCons hExNeg
      have ht' : MSet (.imp (rename (pushNat σ t) p) .bot) := by
        have hEq : subst t (.imp (rename (lift σ) p) .bot) = .imp (rename (pushNat σ t) p) .bot := by
          change Formula.imp (subst t (rename (lift σ) p)) .bot = _
          rw [subst_rename_lift]
        rwa [hEq] at ht
      have hp := h (Quotient.mk (henkinSetoid hCons) t)
      rw [pushValue_mk] at hp
      have hpt := (truth_lemma hCons p (pushNat σ t)).mp hp
      exact (mset_not_mem_iff hCons _).mpr ht' hpt
    · intro hall x
      refine Quotient.inductionOn x (fun t => ?_)
      rw [pushValue_mk, truth_lemma hCons p (pushNat σ t), ← subst_rename_lift]
      exact mset_closed hCons (Γ := [.all (rename (lift σ) p)])
        (fun g hg => by cases hg with | head => exact Or.inr hall | tail _ h' => cases h')
        (ND.allE t (ND.ctx (.head _)))
  | .ex p, σ => by
    constructor
    · rintro ⟨x, hx⟩
      refine Quotient.inductionOn x (fun t ht => ?_) hx
      rw [pushValue_mk, truth_lemma hCons p (pushNat σ t), ← subst_rename_lift] at ht
      exact mset_closed hCons (Γ := [subst t (rename (lift σ) p)])
        (fun g hg => by cases hg with | head => exact Or.inr ht | tail _ h' => cases h')
        (ND.exI t (ND.ctx (.head _)))
    · intro hex
      obtain ⟨t, ht⟩ := mset_ex_witness hCons hex
      refine ⟨Quotient.mk (henkinSetoid hCons) t, ?_⟩
      rw [pushValue_mk, truth_lemma hCons p (pushNat σ t), ← subst_rename_lift]
      exact ht

private theorem eval_congr_bound {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (n : Nat) (s₁ s₂ : Nat → V),
      Bound f n → (∀ i < n, s₁ i = s₂ i) → (eval E f s₁ ↔ eval E f s₂)
  | .bot, _, _, _, _, _ => Iff.rfl
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => by simp [eval, h i hi, h j hj]
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => by simp [eval, h i hi, h j hj]
  | .and a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .or a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .imp a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .all a, n, s₁, s₂, ha, h => by
    constructor
    · intro h1 x
      exact (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp (h1 x)
    · intro h2 x
      exact (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr (h2 x)
  | .ex a, n, s₁, s₂, ha, h => by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr hx⟩

theorem henkin_completeness : Consistent → ∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E := by
  intro hCons
  refine ⟨HenkinV hCons, HenkinE hCons, ⟨Quotient.mk (henkinSetoid hCons) 0⟩, ?_⟩
  intro p hAx s
  have h0 : eval (HenkinE hCons) p (fun i => Quotient.mk (henkinSetoid hCons) (id i)) := by
    rw [truth_lemma hCons p id, rename_id]
    exact mset_axiom hCons hAx
  exact (eval_congr_bound (HenkinE hCons) p 0 s (fun i => Quotient.mk (henkinSetoid hCons) (id i))
    (bound_axiom hAx) (fun _ h => nomatch h)).mpr h0

end DevHenkin

theorem solution : Consistent → ∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E :=
  DevHenkin.henkin_completeness
